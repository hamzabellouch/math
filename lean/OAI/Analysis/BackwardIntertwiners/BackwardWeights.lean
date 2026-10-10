import OAI.Analysis.BackwardIntertwiners.FiberMaps

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal


def plusResidue (x : Base) (m : ℕ) : ℕ := residue m x
def minusResidue (x : Base) (m : ℕ) : ℕ := 2^m-1-residue m x
lemma plusResidue_bounds (x : Base) : ResidueBounds (plusResidue x) := fun m => residue_lt m x
lemma minusResidue_bounds (x : Base) : ResidueBounds (minusResidue x) := by
  intro m
  have hp : 0 < 2^m := pow_pos (by norm_num) _
  dsimp [minusResidue]
  omega


def explicitExponent (x : Base) (j : ℤ) : ℝ :=
  bilateralExponent (plusResidue x) (minusResidue x) j
def explicitBeta (x : Base) (j : ℤ) : ℝ :=
  bilateralBeta (plusResidue x) (minusResidue x) j
def explicitWeight (x : Base) (j : ℤ) : ℝ :=
  bilateralWeight (plusResidue x) (minusResidue x) j

lemma measurable_halfExponent (t : Base → ℕ → ℕ) (ht : ∀ m, Measurable (fun x => t x m))
    (k : ℕ) : Measurable (fun x => halfExponent (t x) k) := by
  dsimp [halfExponent, residueCorrection]
  split_ifs
  · exact measurable_const
  · fun_prop

lemma measurable_plusResidue (m : ℕ) : Measurable (fun x => plusResidue x m) := measurable_residue m
lemma measurable_minusResidue (m : ℕ) : Measurable (fun x => minusResidue x m) :=
  measurable_const.sub (measurable_residue m)
lemma measurable_explicitExponent (j : ℤ) : Measurable (fun x => explicitExponent x j) := by
  cases j with
  | ofNat n => exact measurable_halfExponent plusResidue measurable_plusResidue n
  | negSucc n => exact measurable_halfExponent minusResidue measurable_minusResidue n
lemma measurable_explicitBeta (j : ℤ) : Measurable (fun x => explicitBeta x j) :=
  Real.measurable_exp.comp (measurable_explicitExponent j).neg
lemma measurable_halfSum (t : Base → ℕ → ℕ) (ht : ∀ m, Measurable (fun x => t x m))
    (n : ℕ) : Measurable (fun x => halfSum (t x) n) :=
  Finset.measurable_sum _ (fun k _ => measurable_halfExponent t ht k)
lemma measurable_explicitWeight (j : ℤ) : Measurable (fun x => explicitWeight x j) := by
  cases j with
  | ofNat n => exact Real.measurable_exp.comp (measurable_halfSum plusResidue measurable_plusResidue n).neg
  | negSucc n => exact Real.measurable_exp.comp (measurable_halfSum minusResidue measurable_minusResidue (n+1))
lemma explicitBeta_pos (x : Base) (j : ℤ) : 0 < explicitBeta x j := Real.exp_pos _
lemma explicitWeight_pos (x : Base) (j : ℤ) : 0 < explicitWeight x j := bilateralWeight_pos _ _ _
lemma explicitBeta_le (x : Base) (j : ℤ) : explicitBeta x j ≤ Real.exp (-10) := by
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (bilateralExponent_nonneg _ _ _)
@[simp] lemma explicitBeta_zero (x : Base) : explicitBeta x 0 = Real.exp (-10) := by
  simp [explicitBeta, bilateralBeta, bilateralExponent, halfExponent, residueCorrection]
@[simp] lemma explicitWeight_zero (x : Base) : explicitWeight x 0 = 1 := by
  simp [explicitWeight, bilateralWeight]
@[simp] lemma explicitWeight_neg_one (x : Base) : explicitWeight x (-1) = Real.exp 10 := by
  change Real.exp (halfSum (minusResidue x) 1) = _
  simp [halfSum_succ, halfExponent, residueCorrection]
lemma explicitWeight_ratio (x : Base) (j : ℤ) :
    explicitWeight x (j+1) / explicitWeight x j = explicitBeta x j :=
  bilateralWeight_ratio _ _ _

lemma weightBlock_eventually_ge (M : ℕ) : ∀ᶠ k : ℕ in atTop, M ≤ weightBlock k := by
  filter_upwards [eventually_ge_atTop (8^M)] with k hk
  have h := Nat.le_log_of_pow_le (by norm_num : 1 < 8) hk
  exact h.trans (Nat.le_succ _)

lemma halfExponent_drift {x : Base} (hx : x ∈ goodBase) :
    ∀ᶠ k : ℕ in atTop,
      halfExponent (plusResidue (odometer x)) k - halfExponent (plusResidue x) k = 100 ∧
      halfExponent (minusResidue (odometer x)) k - halfExponent (minusResidue x) k = -100 := by
  obtain ⟨M,hM⟩ := goodBase_eventually_nonexceptional hx
  filter_upwards [weightBlock_eventually_ge M, eventually_ge_atTop 1] with k hk hk1
  have hstep := residue_step (show 1 ≤ weightBlock k by unfold weightBlock; omega) x
  rw [ite_eq_right (hM _ hk)] at hstep
  have hcomp y : ((minusResidue y (weightBlock k)):ℝ) =
      (residueScale k:ℝ)-1-residue (weightBlock k) y := by
    have hr := residue_lt (weightBlock k) y
    have hN : 0 < 2^weightBlock k := pow_pos (by norm_num) _
    dsimp [minusResidue, residueScale]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  dsimp [halfExponent, residueCorrection]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp [plusResidue]
  rw [hcomp, hcomp, hstep]
  push_cast
  constructor <;> ring

lemma halfSum_eventually_affine {t u : ℕ → ℕ} {d : ℝ}
    (hd : ∀ᶠ k : ℕ in atTop, halfExponent u k-halfExponent t k = d) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, halfSum u n-halfSum t n = d*(n:ℝ)+C := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  refine ⟨halfSum u N-halfSum t N-d*(N:ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  induction n, hn using Nat.le_induction with
  | base => ring
  | succ n hn ih =>
    rw [halfSum_succ, halfSum_succ]
    have he := hN n hn
    push_cast
    linarith


def rawBackward (x : Base) (j : ℤ) : ℝ :=
  explicitWeight (odometer x) (j-1) / (explicitWeight x j * Real.exp 10)
lemma rawBackward_pos (x : Base) (j : ℤ) : 0 < rawBackward x j := by
  exact div_pos (explicitWeight_pos _ _) (mul_pos (explicitWeight_pos _ _) (Real.exp_pos _))
@[simp] lemma rawBackward_zero (x : Base) : rawBackward x 0 = 1 := by
  simp [rawBackward, ne_of_gt (Real.exp_pos (10:ℝ))]
lemma measurable_rawBackward (j : ℤ) : Measurable (fun x => rawBackward x j) := by
  exact ((measurable_explicitWeight (j-1)).comp odometer_ergodic.measurable).div
    ((measurable_explicitWeight j).mul_const _)
lemma rawBackward_recurrence (x : Base) (j : ℤ) :
    rawBackward x (j+1)*explicitBeta x j = rawBackward x j*explicitBeta (odometer x) (j-1) := by
  rw [← explicitWeight_ratio x j, ← explicitWeight_ratio (odometer x) (j-1)]
  simp only [rawBackward, add_sub_cancel_right, sub_add_cancel]
  have h₀ := ne_of_gt (explicitWeight_pos x j)
  have h₁ := ne_of_gt (explicitWeight_pos x (j+1))
  have h₂ := ne_of_gt (explicitWeight_pos (odometer x) (j-1))
  field_simp

lemma rawBackward_nat_succ (x : Base) (n : ℕ) :
    rawBackward x (n+1) = Real.exp
      (halfSum (plusResidue x) n - halfSum (plusResidue (odometer x)) n +
        halfExponent (plusResidue x) n - 10) := by
  have he : (n:ℤ)+1 = ((n+1:ℕ):ℤ) := by omega
  unfold rawBackward
  rw [add_sub_cancel_right, he]
  simp only [explicitWeight, bilateralWeight_nat, ← Real.exp_add, ← Real.exp_sub, halfSum_succ]
  congr 1
  ring
lemma rawBackward_neg_nat (x : Base) (n : ℕ) :
    rawBackward x (-(n:ℤ)) = Real.exp
      (halfSum (minusResidue (odometer x)) n - halfSum (minusResidue x) n +
        halfExponent (minusResidue (odometer x)) n - 10) := by
  have he : -(n:ℤ)-1 = -((n+1:ℕ):ℤ) := by omega
  simp only [rawBackward, he, explicitWeight, bilateralWeight_neg_nat,
    ← Real.exp_add, ← Real.exp_sub, halfSum_succ]
  congr 1
  ring

lemma sqrt_error_linear (n : ℕ) : 400*Real.sqrt (n:ℝ) ≤ 45*(n:ℝ)+1000 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp := Real.sqrt_nonneg (n:ℝ)
  nlinarith [sq_nonneg (3*Real.sqrt (n:ℝ)-14)]

lemma halfExponent_linear_upper {t : ℕ → ℕ} (ht : ResidueBounds t) (n : ℕ) :
    halfExponent t n - 10 ≤ 55*(n:ℝ)+1000 := by
  have hh := (residueCorrection_sqrt_bound ht n).trans (sqrt_error_linear n)
  dsimp [halfExponent]
  linarith

lemma tendsto_exp_neg45 (C : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-45*(n:ℝ)+C)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have ht : Tendsto (fun n : ℕ => (45:ℝ)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa only [Function.comp_def, neg_mul] using
    (tendsto_atBot_add_const_right atTop C (tendsto_neg_atTop_atBot.comp ht))

lemma rawBackward_decay {x : Base} (hx : x ∈ goodBase) :
    Tendsto (fun n : ℕ => rawBackward x (n+1)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => rawBackward x (-(n:ℤ))) atTop (𝓝 0) := by
  have hd := halfExponent_drift hx
  obtain ⟨Cp,hCp⟩ := halfSum_eventually_affine (hd.mono (fun _ h => h.1))
  obtain ⟨Cm,hCm⟩ := halfSum_eventually_affine (hd.mono (fun _ h => h.2))
  constructor
  · apply squeeze_zero' (g := fun n : ℕ => Real.exp (-45*(n:ℝ)+(1000-Cp)))
    · exact Filter.Eventually.of_forall fun n => (rawBackward_pos x _).le
    · filter_upwards [hCp] with n hn
      rw [rawBackward_nat_succ]
      apply Real.exp_le_exp.mpr
      have hu := halfExponent_linear_upper (plusResidue_bounds x) n
      linarith
    · exact tendsto_exp_neg45 _
  · apply squeeze_zero' (g := fun n : ℕ => Real.exp (-45*(n:ℝ)+(1000+Cm)))
    · exact Filter.Eventually.of_forall fun n => (rawBackward_pos x _).le
    · filter_upwards [hCm] with n hn
      rw [rawBackward_neg_nat]
      apply Real.exp_le_exp.mpr
      have hu := halfExponent_linear_upper (minusResidue_bounds (odometer x)) n
      linarith
    · exact tendsto_exp_neg45 _

lemma rawBackward_bddAbove {x : Base} (hx : x ∈ goodBase) : BddAbove (Set.range (rawBackward x)) := by
  obtain ⟨C,hC⟩ := (rawBackward_decay hx).1.bddAbove_range
  obtain ⟨D,hD⟩ := (rawBackward_decay hx).2.bddAbove_range
  refine ⟨max C D, ?_⟩
  rintro y ⟨j,rfl⟩
  by_cases hj : 1 ≤ j
  · have he : j = ((j-1).toNat:ℤ)+1 := by omega
    rw [he]
    exact (hC (Set.mem_range_self _)).trans (le_max_left _ _)
  · have he : j = -((-j).toNat:ℤ) := by omega
    rw [he]
    exact (hD (Set.mem_range_self _)).trans (le_max_right _ _)


def backwardBound (x : Base) : ℝ := ⨆ j : ℤ, rawBackward x j
lemma measurable_backwardBound : Measurable backwardBound :=
  Measurable.iSup measurable_rawBackward
lemma backwardBound_ge_one {x : Base} (hx : x ∈ goodBase) : 1 ≤ backwardBound x := by
  rw [← rawBackward_zero x]
  exact le_ciSup (rawBackward_bddAbove hx) 0
lemma rawBackward_le_bound {x : Base} (hx : x ∈ goodBase) (j : ℤ) :
    rawBackward x j ≤ backwardBound x := le_ciSup (rawBackward_bddAbove hx) j



def backwardCoeff (x : Base) (j : ℤ) : ℝ := by
  classical
  exact if x ∈ goodBase then rawBackward x j / backwardBound x else 0
lemma measurable_backwardCoeff (j : ℤ) : Measurable (fun x => backwardCoeff x j) := by
  exact Measurable.ite measurableSet_goodBase
    ((measurable_rawBackward j).div measurable_backwardBound) measurable_const
lemma backwardCoeff_bounds (x : Base) (j : ℤ) :
    0 ≤ backwardCoeff x j ∧ backwardCoeff x j ≤ 1 := by
  unfold backwardCoeff
  split_ifs with hx
  · have hL : 0 < backwardBound x := lt_of_lt_of_le (by norm_num) (backwardBound_ge_one hx)
    exact ⟨(div_pos (rawBackward_pos x j) hL).le, (div_le_one hL).mpr (rawBackward_le_bound hx j)⟩
  · norm_num
lemma backwardCoeff_pos {x : Base} (hx : x ∈ goodBase) (j : ℤ) : 0 < backwardCoeff x j := by
  rw [backwardCoeff, ite_eq_left hx]
  exact div_pos (rawBackward_pos x j) (lt_of_lt_of_le (by norm_num) (backwardBound_ge_one hx))
lemma backwardCoeff_recurrence (x : Base) (j : ℤ) :
    backwardCoeff x (j+1)*explicitBeta x j = backwardCoeff x j*explicitBeta (odometer x) (j-1) := by
  unfold backwardCoeff
  split_ifs with hx
  · simpa only [div_mul_eq_mul_div] using congrArg (fun y => y/backwardBound x) (rawBackward_recurrence x j)
  · simp
lemma backwardCoeff_ae_pos : ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, 0 < backwardCoeff x j :=
  ae_goodBase.mono fun _ hx => backwardCoeff_pos hx


end
end BackwardIntertwiners

end OAI
