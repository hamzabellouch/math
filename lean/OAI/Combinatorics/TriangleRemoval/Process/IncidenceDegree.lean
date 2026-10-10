import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

theorem algebra_norm_exp_le {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hs := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have ht := NormedSpace.expSeries_summable' (𝕂 := ℝ) (‖x‖ : ℝ)
  rw [NormedSpace.exp_eq_tsum ℝ]
  calc
    _ ≤ ∑' k : ℕ, ‖((k.factorial : ℝ)⁻¹) • x ^ k‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, (k.factorial : ℝ)⁻¹ * ‖x‖ ^ k := by
      apply hs.tsum_le_tsum _ ht
      intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      exact mul_le_mul_of_nonneg_left (norm_pow_le x k) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Real.exp ‖x‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      rfl

theorem rectangular_power_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (k : ℕ) :
    (U * V) ^ k * U = U * (V * U) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih]
    simp only [pow_succ', Matrix.mul_assoc]

theorem averaging_shift_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (W : Matrix ι ι ℝ) (hW : ‖W‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (1 + W))‖ ≤ 1 := by
  have hc : Commute ((-s) • (1 : Matrix ι ι ℝ)) ((-s) • W) :=
    (Commute.one_left W).smul_left (-s) |>.smul_right (-s)
  rw [smul_add]
  have hadd : NormedSpace.exp (((-s) • (1 : Matrix ι ι ℝ)) + (-s) • W) =
      NormedSpace.exp ((-s) • (1 : Matrix ι ι ℝ)) * NormedSpace.exp ((-s) • W) :=
    Matrix.exp_add_of_commute _ _ hc
  rw [hadd]
  have he : NormedSpace.exp ((-s) • (1 : Matrix ι ι ℝ)) =
      Real.exp (-s) • (1 : Matrix ι ι ℝ) := by
    have hh := NormedSpace.algebraMap_exp_comm (𝔸 := Matrix ι ι ℝ) (-s)
    change _ = _ at hh
    convert hh.symm using 1 <;> simp [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]
    rfl
  rw [he, smul_mul_assoc, one_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-s) * Real.exp ‖(-s) • W‖ :=
      mul_le_mul_of_nonneg_left (algebra_norm_exp_le _) (Real.exp_pos _).le
    _ ≤ Real.exp (-s) * Real.exp s := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
      simpa using mul_le_mul_of_nonneg_left hW hs
    _ = 1 := by rw [← Real.exp_add]; simp

theorem rectangular_exp_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (s : ℝ) :
    NormedSpace.exp (s • (U * V)) * U = U * NormedSpace.exp (s • (V * U)) := by
  let L := (mulLeftLinearMap κ ℝ U).toContinuousLinearMap
  let R := (mulRightLinearMap ι ℝ U).toContinuousLinearMap
  have hL := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • (V * U)))
  have hR := R.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • (U * V)))
  have heq : (fun k : ℕ => R ((k.factorial : ℝ)⁻¹ • (s • (U * V)) ^ k)) =
      (fun k : ℕ => L ((k.factorial : ℝ)⁻¹ • (s • (V * U)) ^ k)) := by
    funext k
    change ((k.factorial : ℝ)⁻¹ • (s • (U * V)) ^ k) * U =
      U * ((k.factorial : ℝ)⁻¹ • (s • (V * U)) ^ k)
    simp only [smul_pow, Matrix.smul_mul, Matrix.mul_smul, rectangular_power_swap]
  rw [heq] at hR
  exact hR.unique hL

theorem hasDerivAt_rectangular_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((-t) • (U * V)))
      (-(U * NormedSpace.exp ((-s) • (V * U)) * V)) s := by
  have hh := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (U * V) (-s)).scomp s
    ((hasDerivAt_id s).neg)
  have heq : -(U * NormedSpace.exp ((-s) • (V * U)) * V) =
      (-1 : ℝ) • (NormedSpace.exp ((-s) • (U * V)) * (U * V)) := by
    rw [neg_one_smul, ← Matrix.mul_assoc, rectangular_exp_swap]
  rw [heq]
  convert hh using 1 <;> rfl

theorem rectangular_semigroup_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (W : Matrix κ κ ℝ)
    (hVU : V * U = 1 + W) (hW : ‖W‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (U * V))‖ ≤ 1 + s * (‖U‖ * ‖V‖) := by
  let f : ℝ → Matrix ι ι ℝ := fun t => NormedSpace.exp ((-t) • (U * V))
  let g : ℝ → Matrix ι ι ℝ := fun t => -(U * NormedSpace.exp ((-t) • (V * U)) * V)
  have hd : ∀ t, HasDerivAt f (g t) t := fun t => hasDerivAt_rectangular_exp U V t
  have hg : Continuous g := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun t _ => hd t) (hg.intervalIntegrable 0 s)
  have hzero : f 0 = 1 := by simp [f, NormedSpace.exp_zero]
  rw [hzero] at hi
  have hn : ‖∫ t in (0 : ℝ)..s, g t‖ ≤ (‖U‖ * ‖V‖) * s := by
    have hb : ∀ t ∈ Set.uIoc 0 s, ‖g t‖ ≤ ‖U‖ * ‖V‖ := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (Set.mem_Ioc.mp (Set.uIoc_of_le hs ▸ ht)).1
      have he := averaging_shift_exp_bound W hW t ht0
      rw [← hVU] at he
      calc
        ‖g t‖ = ‖U * NormedSpace.exp ((-t) • (V * U)) * V‖ := norm_neg _
        _ ≤ (‖U‖ * ‖NormedSpace.exp ((-t) • (V * U))‖) * ‖V‖ :=
          (Matrix.linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ (‖U‖ * 1) * ‖V‖ := by gcongr
        _ = ‖U‖ * ‖V‖ := by ring
    simpa only [sub_zero, abs_of_nonneg hs] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have ht : f s = 1 + ∫ t in (0 : ℝ)..s, g t := by rw [hi]; abel
  calc
    ‖f s‖ = ‖1 + ∫ t in (0 : ℝ)..s, g t‖ := congrArg norm ht
    _ ≤ ‖(1 : Matrix ι ι ℝ)‖ + ‖∫ t in (0 : ℝ)..s, g t‖ := norm_add_le _ _
    _ ≤ 1 + (‖U‖ * ‖V‖) * s := by rw [norm_one]; gcongr
    _ = 1 + s * (‖U‖ * ‖V‖) := by ring

theorem matrix_norm_le_of_row_abs_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨c, hc⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ c
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h i
  exact_mod_cast hh

def incidenceDegree {ι κ : Type*} [Fintype ι] (U : Matrix ι κ ℝ) (v : κ) : ℝ :=
  ∑ e, U e v

noncomputable def starAverage {ι κ : Type*} [Fintype ι] (U : Matrix ι κ ℝ) :
    Matrix κ ι ℝ := fun v e => U e v / incidenceDegree U v

theorem incidence_norm_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hrow : ∀ e, ∑ v, U e v = 2) : ‖U‖ ≤ 2 := by
  apply matrix_norm_le_of_row_abs_sum_le U 2 (by norm_num)
  intro e
  simpa only [abs_of_nonneg (hU e _), hrow e] using le_refl (2 : ℝ)

theorem starAverage_nonneg {ι κ : Type*} [Fintype ι]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v) (v : κ) (e : ι) :
    0 ≤ starAverage U v e := by
  exact div_nonneg (hU e v) (Finset.sum_nonneg fun e _ => hU e v)

theorem starAverage_row_sum {ι κ : Type*} [Fintype ι]
    (U : Matrix ι κ ℝ) (hdeg : ∀ v, 0 < incidenceDegree U v) (v : κ) :
    ∑ e, starAverage U v e = 1 := by
  simp only [starAverage, ← Finset.sum_div]
  change incidenceDegree U v / incidenceDegree U v = 1
  exact div_self (ne_of_gt (hdeg v))

theorem starAverage_norm_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hdeg : ∀ v, 0 < incidenceDegree U v) : ‖starAverage U‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ 1 zero_le_one
  intro v
  simpa only [abs_of_nonneg (starAverage_nonneg U hU v _), starAverage_row_sum U hdeg] using le_refl (1 : ℝ)

theorem starAverage_mul_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hidem : ∀ e v, U e v * U e v = U e v)
    (hdeg : ∀ v, 0 < incidenceDegree U v) (v : κ) :
    (starAverage U * U) v v = 1 := by
  simp only [Matrix.mul_apply, starAverage]
  simp_rw [div_mul_eq_mul_div, hidem]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (hdeg v))

theorem starAverage_neighbor_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hidem : ∀ e v, U e v * U e v = U e v)
    (hrow : ∀ e, ∑ v, U e v = 2)
    (hdeg : ∀ v, 0 < incidenceDegree U v) : ‖starAverage U * U - 1‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ 1 zero_le_one
  intro v
  have hnonneg : ∀ w, 0 ≤ (starAverage U * U - (1 : Matrix κ κ ℝ)) v w := by
    intro w
    by_cases hvw : v = w
    · subst w
      simp [starAverage_mul_diagonal U hidem hdeg]
    · simp only [Matrix.sub_apply, Matrix.one_apply_ne hvw, sub_zero, Matrix.mul_apply]
      exact Finset.sum_nonneg fun e _ => mul_nonneg (starAverage_nonneg U hU v e) (hU e w)
  have htotal : ∑ w, (starAverage U * U) v w = 2 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow, ← Finset.sum_mul, starAverage_row_sum U hdeg, one_mul]
  calc
    ∑ j, |(starAverage U * U - (1 : Matrix κ κ ℝ)) v j| = ∑ j, (starAverage U * U - (1 : Matrix κ κ ℝ)) v j := by
      apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (hnonneg j)
    _ = 1 := by simp [Matrix.sub_apply, Finset.sum_sub_distrib, htotal, Matrix.one_apply]; norm_num
    _ ≤ 1 := le_rfl

theorem star_semigroup_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hidem : ∀ e v, U e v * U e v = U e v)
    (hrow : ∀ e, ∑ v, U e v = 2)
    (hdeg : ∀ v, 0 < incidenceDegree U v) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (U * starAverage U))‖ ≤ 1 + 2 * s := by
  have hb := rectangular_semigroup_bound U (starAverage U) (starAverage U * U - 1)
    (by abel) (starAverage_neighbor_norm U hU hidem hrow hdeg) s hs
  calc
    _ ≤ 1 + s * (‖U‖ * ‖starAverage U‖) := hb
    _ ≤ 1 + s * (2 * 1) := by
      gcongr
      · exact incidence_norm_le_two U hU hrow
      · exact starAverage_norm_le_one U hU hdeg
    _ = 1 + 2 * s := by ring

end SharpTerminalLeave

end
end

end OAI
