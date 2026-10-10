import OAI.MathematicalPhysics.Heisenberg.SpinDirected

namespace OAI

section
noncomputable section

open scoped Matrix Matrix.Norms.Operator
namespace Heisenberg.Heat
open MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

def kernel (G : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (t • G)

lemma _root_.OAI.Heisenberg.MatrixContraction.DoublySubstochastic.one : DoublySubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · intro i; simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]; norm_num
  · intro j; simp only [Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; norm_num

lemma _root_.OAI.Heisenberg.MatrixContraction.DoublySubstochastic.pow {P : Matrix V V ℝ} (hP : DoublySubstochastic P) (n : ℕ) :
    DoublySubstochastic (P ^ n) := by
  induction n with
  | zero => simpa using DoublySubstochastic.one (V := V)
  | succ n ih => simpa only [pow_succ] using ih.mul hP

def entry (i j : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

omit [DecidableEq V] in
@[simp] lemma entry_apply (i j : V) (P : Matrix V V ℝ) : entry i j P = P i j := rfl

lemma exp_scalar (a : ℝ) :
    NormedSpace.exp (a • (1 : Matrix V V ℝ)) = Real.exp a • 1 := by
  have result := (NormedSpace.algebraMap_exp_comm (𝔸 := Matrix V V ℝ) a).symm
  simp only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] at result
  convert! result

lemma uniformization (P : Matrix V V ℝ) (a : ℝ) :
    NormedSpace.exp (a • (P - 1)) = Real.exp (-a) • NormedSpace.exp (a • P) := by
  have he : a • (P - 1) = (-a) • (1 : Matrix V V ℝ) + a • P := by
    simp only [smul_sub, neg_smul]; abel
  rw [he, Matrix.exp_add_of_commute, exp_scalar, smul_mul_assoc, one_mul]
  exact ((Commute.one_left P).smul_left (-a)).smul_right a

lemma exp_series (P : Matrix V V ℝ) (a : ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * a ^ n) • P ^ n)
      (NormedSpace.exp (a • P)) := by
  have result := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • P)
  simp only [smul_pow, smul_smul] at result
  convert! result

lemma exp_sub_identity_substochastic {P : Matrix V V ℝ}
    (hP : DoublySubstochastic P) {a : ℝ} (ha : 0 ≤ a) :
    DoublySubstochastic (NormedSpace.exp (a • (P - 1))) := by
  rw [uniformization]
  have hs := exp_series P a
  have hw : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * a ^ n) (Real.exp a) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a)
  have hn (n : ℕ) : 0 ≤ (n.factorial : ℝ)⁻¹ * a ^ n := by positivity
  have hnorm : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  constructor
  · intro i j
    change 0 ≤ Real.exp (-a) * NormedSpace.exp (a • P) i j
    apply mul_nonneg (Real.exp_pos _).le
    exact HasSum.nonneg (fun n => by
      change 0 ≤ ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j
      exact mul_nonneg (hn n) ((hP.pow n).nonneg i j)) ((entry i j).hasSum hs)
  · intro i
    have hb : (∑ j, NormedSpace.exp (a • P) i j) ≤ Real.exp a := by
      let row : Matrix V V ℝ →L[ℝ] ℝ := ∑ j : V, entry i j
      have hr := row.hasSum hs
      simp only [row, sum_apply, entry_apply, Matrix.smul_apply, smul_eq_mul] at hr
      apply hasSum_le (fun n => ?_) hr hw
      change (∑ j, ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j) ≤ _
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (hn n) ((hP.pow n).row i)
    change (∑ j, Real.exp (-a) * NormedSpace.exp (a • P) i j) ≤ 1
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq hnorm
  · intro j
    have hb : (∑ i, NormedSpace.exp (a • P) i j) ≤ Real.exp a := by
      let col : Matrix V V ℝ →L[ℝ] ℝ := ∑ i : V, entry i j
      have hr := col.hasSum hs
      simp only [col, sum_apply, entry_apply, Matrix.smul_apply, smul_eq_mul] at hr
      apply hasSum_le (fun n => ?_) hr hw
      change (∑ i, ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j) ≤ _
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (hn n) ((hP.pow n).col j)
    change (∑ i, Real.exp (-a) * NormedSpace.exp (a • P) i j) ≤ 1
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq hnorm

structure SubMarkovGenerator (G : Matrix V V ℝ) : Prop where
  offdiag : ∀ i j, i ≠ j → 0 ≤ G i j
  row : ∀ i, ∑ j, G i j ≤ 0
  col : ∀ j, ∑ i, G i j ≤ 0

lemma uniformized_substochastic {G : Matrix V V ℝ} (hG : SubMarkovGenerator G)
    {c : ℝ} (hc : 0 < c) (hdiag : ∀ i, -G i i ≤ c) :
    DoublySubstochastic (1 + c⁻¹ • G) := by
  constructor
  · intro i j
    change 0 ≤ (1 : Matrix V V ℝ) i j + c⁻¹ * G i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.one_apply_eq]
      have : -G i i / c ≤ 1 := (div_le_iff₀ hc).mpr (by simpa using hdiag i)
      rw [neg_div] at this
      rw [mul_comm, ← div_eq_mul_inv]
      linarith
    · simp only [Matrix.one_apply_ne h, zero_add]
      exact mul_nonneg (inv_nonneg.mpr hc.le) (hG.offdiag i j h)
  · intro i
    change (∑ j, ((1 : Matrix V V ℝ) i j + c⁻¹ * G i j)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Matrix.one_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, add_le_iff_nonpos_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hG.row i)
  · intro j
    change (∑ i, ((1 : Matrix V V ℝ) i j + c⁻¹ * G i j)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Matrix.one_apply, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, add_le_iff_nonpos_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hG.col j)

theorem kernel_substochastic {G : Matrix V V ℝ} (hG : SubMarkovGenerator G)
    {t : ℝ} (ht : 0 ≤ t) : DoublySubstochastic (kernel G t) := by
  let c : ℝ := 1 + ∑ i, |G i i|
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hd (i : V) : -G i i ≤ c := by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (G j j)) (Finset.mem_univ i)
    have := neg_le_abs (G i i)
    dsimp [c]; linarith
  have hp := uniformized_substochastic hG hc hd
  have he : (t * c) • ((1 + c⁻¹ • G) - 1) = t • G := by
    rw [add_sub_cancel_left, smul_smul]
    congr 1
    field_simp
  simpa only [he, kernel] using exp_sub_identity_substochastic hp (mul_nonneg ht hc.le)

def generator (r : Matrix V V ℝ) (κ : V → ℝ) : Matrix V V ℝ :=
  r - Matrix.diagonal (fun i => (∑ j, r i j) + κ i)

lemma generator_subMarkov (r : Matrix V V ℝ) (κ : V → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (hs : r.IsSymm) (hk : ∀ i, 0 ≤ κ i) :
    SubMarkovGenerator (generator r κ) := by
  constructor
  · intro i j hij
    simpa [generator, Matrix.diagonal_apply_ne _ hij] using hr i j
  · intro i
    simp only [generator, Matrix.sub_apply, Finset.sum_sub_distrib,
      Matrix.diagonal_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hk i]
  · intro j
    have he : ∑ i, r i j = ∑ i, r j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (congrFun (congrFun hs i) j).symm
    simp only [generator, Matrix.sub_apply, Finset.sum_sub_distrib,
      Matrix.diagonal_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [he]
    linarith [hk j]

lemma generator_action (r : Matrix V V ℝ) (κ v : V → ℝ) (i : V) :
    (generator r κ).mulVec v i = ∑ j, r i j * (v j - v i) - κ i * v i := by
  change (∑ j, (r i j - (Matrix.diagonal (fun i => (∑ j, r i j) + κ i)) i j) * v j) = _
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

def energy (r : Matrix V V ℝ) (κ v : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, r i j * (v i - v j) ^ 2 + ∑ i, κ i * v i ^ 2

omit [DecidableEq V] in
lemma energy_nonneg (r : Matrix V V ℝ) (κ v : V → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (hk : ∀ i, 0 ≤ κ i) : 0 ≤ energy r κ v := by
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (hr i j) (sq_nonneg _)))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hk i) (sq_nonneg _))

lemma dirichlet_identity (r : Matrix V V ℝ) (κ v : V → ℝ) (hs : r.IsSymm) :
    dot v ((generator r κ).mulVec v) = -energy r κ v := by
  let A : ℝ := ∑ i, ∑ j, v i * r i j * (v j - v i)
  have hswap : A = ∑ i, ∑ j, v j * r i j * (v i - v j) := by
    dsimp [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show r j i = r i j from congrFun (congrFun hs i) j]
  have htwo : 2 * A = -(∑ i, ∑ j, r i j * (v i - v j) ^ 2) := by
    calc
      2 * A = A + A := by ring
      _ = A + ∑ i, ∑ j, v j * r i j * (v i - v j) := congrArg (A + ·) hswap
      _ = ∑ i, ∑ j, (v i * r i j * (v j - v i) +
          v j * r i j * (v i - v j)) := by
        simp only [A, Finset.sum_add_distrib]
      _ = _ := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hd : dot v ((generator r κ).mulVec v) = A - ∑ i, κ i * v i ^ 2 := by
    calc
      _ = ∑ i, ((∑ j, v i * r i j * (v j - v i)) - κ i * v i ^ 2) := by
        unfold dot
        apply Finset.sum_congr rfl
        intro i _
        rw [generator_action, mul_sub, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          ring
        · ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hd]
  dsimp [energy]
  linarith

lemma kernel_derivative (G : Matrix V V ℝ) (v : V → ℝ) (t : ℝ) (i : V) :
    HasDerivAt (fun u => (kernel G u).mulVec v i)
      (G.mulVec ((kernel G t).mulVec v) i) t := by
  have h (j : V) : HasDerivAt (fun u => kernel G u i j) ((G * kernel G t) i j) t := by
    have result :=
      (entry i j).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' G t)
    simp only [Function.comp_def, entry_apply] at result
    convert! result
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (h j).mul_const (v j))
  change HasDerivAt (fun u => (kernel G u).mulVec v i) (((G * kernel G t).mulVec v) i) t at hd
  simpa only [Matrix.mulVec_mulVec] using hd

theorem dissipation (r : Matrix V V ℝ) (κ v : V → ℝ) (hs : r.IsSymm) (t : ℝ) :
    HasDerivAt (fun u => squareNorm ((kernel (generator r κ) u).mulVec v))
      (-2 * energy r κ ((kernel (generator r κ) t).mulVec v)) t := by
  let w := (kernel (generator r κ) t).mulVec v
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (kernel_derivative (generator r κ) v t i).pow 2)
  have he : (∑ i, 2 * w i ^ (2 - 1) * ((generator r κ).mulVec w) i) =
      -2 * energy r κ w := by
    simp only [show 2 - 1 = (1 : ℕ) from rfl, pow_one]
    rw [show (∑ i, 2 * w i * ((generator r κ).mulVec w) i) =
      2 * dot w ((generator r κ).mulVec w) by
      simp only [dot, Finset.mul_sum, mul_assoc]]
    rw [dirichlet_identity r κ w hs]; ring
  exact he ▸ hd

end Heisenberg.Heat

noncomputable section
open Filter Topology
namespace ExchangeLimit

variable {E : Type*} [NormedRing E] [NormOneClass E]

lemma contraction_power_difference (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ n * ‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : ‖b^n‖ ≤ 1 := (norm_pow_le b n).trans (pow_le_one₀ (norm_nonneg _) hb)
    have he : a^(n+1)-b^(n+1) = a*(a^n-b^n)+(a-b)*b^n := by
      rw [pow_succ',pow_succ']; noncomm_ring
    rw [he]
    calc
      _ ≤ ‖a‖*‖a^n-b^n‖+‖a-b‖*‖b^n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖a^n-b^n‖ + ‖a-b‖ := add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) ha)
        (mul_le_of_le_one_right (norm_nonneg _) hbn)
      _ ≤ (n:ℝ)*‖a-b‖+‖a-b‖ := by linarith
      _ = _ := by push_cast; ring

variable [NormedAlgebra ℝ E] [CompleteSpace E]

theorem contraction_product_limit (f : ℝ → E) (D : E)
    (h0 : f 0 = 1) (hd : HasDerivAt f D 0)
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ 1)
    (hD : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • D)‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (f (t/(n+1)))^(n+1)) atTop (nhds (NormedSpace.exp (t • D))) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let g : ℝ → E := fun s => f s - NormedSpace.exp (s • D)
  have hg0 : g 0 = 0 := by simp [g,h0]
  have hgd : HasDerivAt g 0 0 := by
    have h := hd.sub (hasDerivAt_exp_smul_const D (0:ℝ))
    change HasDerivAt g _ _ at h
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul,sub_self] using h
  have hs : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have herr : Tendsto (fun n : ℕ => ((n+1:ℝ)) * ‖g (t/(n+1:ℝ))‖) atTop (nhds 0) := by
    by_cases ht0 : t = 0
    · simp [ht0,hg0]
    · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hsl := hgd.tendsto_slope_zero
      have hsn : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (𝓝[≠] (0:ℝ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hs, Filter.Eventually.of_forall ?_⟩
        intro n
        simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
        exact div_ne_zero ht0 (by positivity)
      have hh := (hsl.comp hsn).norm.const_mul t
      convert hh using 1
      · funext n
        simp only [Function.comp_apply,hg0,sub_zero,zero_add,norm_smul,Real.norm_eq_abs]
        rw [abs_of_pos (inv_pos.mpr (div_pos hpos (by positivity)))]
        field_simp
      · simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ herr
  intro n
  have hpn : 0 < (n+1:ℝ) := by positivity
  have hexp : (NormedSpace.exp ((t/(n+1:ℝ)) • D))^(n+1) = NormedSpace.exp (t • D) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← hexp]
  simpa only [g,Nat.cast_add,Nat.cast_one] using contraction_power_difference
    (f (t/(n+1:ℝ))) (NormedSpace.exp ((t/(n+1:ℝ)) • D))
    (hf _ (div_nonneg ht hpn.le)) (hD _ (div_nonneg ht hpn.le)) (n+1)

end ExchangeLimit

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma substochastic_norm_le {P : Matrix V V ℝ} (hP : DoublySubstochastic P) : ‖P‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i : V => ∑ j : V, ‖P i j‖₊ : ℝ≥0) : ℝ) ≤ (1:ℝ≥0)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg (hP.nonneg i _),
    NNReal.coe_one] using hP.row i

def permutationMatrix (σ : Equiv.Perm V) : Matrix V V ℝ := fun i j => if σ j = i then 1 else 0

lemma permutationMatrix_substochastic (σ : Equiv.Perm V) :
    DoublySubstochastic (permutationMatrix σ) := by
  unfold permutationMatrix
  simpa only [Option.some.injEq] using of_partial_permutation (fun i => some (σ i)) (fun i j a hi hj =>
    σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm))

@[simp] lemma permutationMatrix_col (σ : Equiv.Perm V) (j : V) :
    ∑ i, permutationMatrix σ i j = 1 := by simp [permutationMatrix]

@[simp] lemma permutationMatrix_row (σ : Equiv.Perm V) (i : V) :
    ∑ j, permutationMatrix σ i j = 1 := by
  simp only [permutationMatrix,← σ.eq_symm_apply]
  simp

lemma permutationMatrix_mulVec (σ : Equiv.Perm V) (v : V → ℝ) (i : V) :
    (permutationMatrix σ).mulVec v i = v (σ.symm i) := by
  simp [Matrix.mulVec,dotProduct,permutationMatrix,← σ.eq_symm_apply]

def bernoulliStep (r : ℝ) (σ : Equiv.Perm V) (t : ℝ) : Matrix V V ℝ :=
  Real.exp (-r*t) • 1 + (1-Real.exp (-r*t)) • permutationMatrix σ

omit [Fintype V] in
lemma bernoulliStep_zero (r : ℝ) (σ : Equiv.Perm V) : bernoulliStep r σ 0 = 1 := by
  simp [bernoulliStep]

lemma bernoulliStep_substochastic (r : ℝ) (hr : 0 ≤ r) (σ : Equiv.Perm V)
    (t : ℝ) (ht : 0 ≤ t) : DoublySubstochastic (bernoulliStep r σ t) := by
  have he : Real.exp (-r*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hp := weighted_average (V := V)
    (fun b : Bool => if b then Real.exp (-r*t) else 1-Real.exp (-r*t))
    (fun b => by
      cases b
      · exact sub_nonneg.mpr he
      · exact (Real.exp_pos _).le)
    (by simp) (fun b : Bool => if b then 1 else permutationMatrix σ)
    (fun b => by cases b; exact permutationMatrix_substochastic σ; exact DoublySubstochastic.one)
  change DoublySubstochastic (fun i j => Real.exp (-r*t) * (1:Matrix V V ℝ) i j +
    (1-Real.exp (-r*t)) * permutationMatrix σ i j)
  simpa only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false] using hp

lemma bernoulliStep_col (r : ℝ) (σ : Equiv.Perm V) (t : ℝ) (j : V) :
    ∑ i, bernoulliStep r σ t i j = 1 := by
  simp only [bernoulliStep,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,← Finset.mul_sum,permutationMatrix_col]
  simp [Matrix.one_apply]

lemma bernoulliStep_derivative (r : ℝ) (σ : Equiv.Perm V) :
    HasDerivAt (bernoulliStep r σ) (r • (permutationMatrix σ - 1)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-r*t)) (-r) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul (-r)).exp using 1 <;> simp
  have h := (hd.smul_const (1 : Matrix V V ℝ)).fun_add
    ((hasDerivAt_const (0:ℝ) 1).fun_sub hd |>.smul_const (permutationMatrix σ))
  change HasDerivAt (bernoulliStep r σ) _ _ at h
  convert h using 1
  simp [smul_sub,neg_smul]; abel

abbrev Clock (V : Type*) := ℝ≥0 × Equiv.Perm V

def meshStep : List (Clock V) → ℝ → Matrix V V ℝ
  | [], _ => 1
  | e::L,t => bernoulliStep e.1 e.2 t * meshStep L t

def clockGenerator : List (Clock V) → Matrix V V ℝ
  | [] => 0
  | e::L => (e.1:ℝ) • (permutationMatrix e.2 - 1) + clockGenerator L

lemma meshStep_zero (L : List (Clock V)) : meshStep L 0 = 1 := by
  induction L with
  | nil => rfl
  | cons e L ih => simp [meshStep,bernoulliStep_zero,ih]

lemma meshStep_substochastic (L : List (Clock V)) (t : ℝ) (ht : 0 ≤ t) :
    DoublySubstochastic (meshStep L t) := by
  induction L with
  | nil => exact DoublySubstochastic.one
  | cons e L ih => exact (bernoulliStep_substochastic _ e.1.property _ t ht).mul ih

lemma meshStep_derivative (L : List (Clock V)) :
    HasDerivAt (meshStep L) (clockGenerator L) 0 := by
  induction L with
  | nil => exact hasDerivAt_const _ _
  | cons e L ih =>
    have h := (bernoulliStep_derivative (e.1:ℝ) e.2).fun_mul ih
    change HasDerivAt (meshStep (e::L)) _ _ at h
    simpa only [clockGenerator,meshStep_zero,bernoulliStep_zero,mul_one,one_mul] using h

lemma clockGenerator_subMarkov (L : List (Clock V)) : SubMarkovGenerator (clockGenerator L) := by
  induction L with
  | nil => exact ⟨by simp [clockGenerator],by simp [clockGenerator],by simp [clockGenerator]⟩
  | cons e L ih =>
    have hp := permutationMatrix_substochastic e.2
    constructor
    · intro i j hij
      change 0 ≤ (e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j
      rw [Matrix.one_apply_ne hij,sub_zero]
      exact add_nonneg (mul_nonneg e.1.property (hp.nonneg i j)) (ih.offdiag i j hij)
    · intro i
      change (∑ j, ((e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j)) ≤ 0
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,permutationMatrix_row]
      simpa [Matrix.one_apply] using ih.row i
    · intro j
      change (∑ i, ((e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j)) ≤ 0
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,permutationMatrix_col]
      simpa [Matrix.one_apply] using ih.col j

theorem mesh_converges [Nonempty V] (L : List (Clock V)) (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto (fun n : ℕ => (meshStep L (t/(n+1:ℝ)))^(n+1)) Filter.atTop
      (nhds (NormedSpace.exp (t • clockGenerator L))) := by
  apply ExchangeLimit.contraction_product_limit _ _ (meshStep_zero L) (meshStep_derivative L)
    (fun u hu => substochastic_norm_le (meshStep_substochastic L u hu))
    (fun u hu => substochastic_norm_le (kernel_substochastic (clockGenerator_subMarkov L) hu)) t ht

end Heisenberg.ExchangeMatrix
end

noncomputable section
open Filter Topology
namespace ExchangeLimit
variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E]
theorem local_contraction_product_limit (f : ℝ → E) (D : E)
    (h0 : f 0 = 1) (hd : HasDerivAt f D 0)
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), 0 ≤ t → ‖f t‖ ≤ 1)
    (hD : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • D)‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (f (t/(n+1)))^(n+1)) atTop (nhds (NormedSpace.exp (t • D))) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let g : ℝ → E := fun s => f s - NormedSpace.exp (s • D)
  have hg0 : g 0 = 0 := by simp [g,h0]
  have hgd : HasDerivAt g 0 0 := by
    have h := hd.sub (hasDerivAt_exp_smul_const D (0:ℝ))
    change HasDerivAt g _ _ at h
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul,sub_self] using h
  have hs : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have herr : Tendsto (fun n : ℕ => ((n+1:ℝ)) * ‖g (t/(n+1:ℝ))‖) atTop (nhds 0) := by
    by_cases ht0 : t = 0
    · simp [ht0,hg0]
    · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hsl := hgd.tendsto_slope_zero
      have hsn : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (𝓝[≠] (0:ℝ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hs, Filter.Eventually.of_forall ?_⟩
        intro n
        simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
        exact div_ne_zero ht0 (by positivity)
      have hh := (hsl.comp hsn).norm.const_mul t
      convert hh using 1
      · funext n
        simp only [Function.comp_apply,hg0,sub_zero,zero_add,norm_smul,Real.norm_eq_abs]
        rw [abs_of_pos (inv_pos.mpr (div_pos hpos (by positivity)))]
        field_simp
      · simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ herr
  filter_upwards [hs.eventually hf] with n hn
  have hpn : 0 < (n+1:ℝ) := by positivity
  have hexp : (NormedSpace.exp ((t/(n+1:ℝ)) • D))^(n+1) = NormedSpace.exp (t • D) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← hexp]
  simpa only [g,Nat.cast_add,Nat.cast_one] using contraction_power_difference
    (f (t/(n+1:ℝ))) (NormedSpace.exp ((t/(n+1:ℝ)) • D))
    (hn (div_nonneg ht hpn.le)) (hD _ (div_nonneg ht hpn.le)) (n+1)

end ExchangeLimit

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [fV : Fintype V] [DecidableEq V]

def linearStep (r : ℝ) (σ : Equiv.Perm V) (t : ℝ) : Matrix V V ℝ :=
  (1-r*t) • 1 + (r*t) • permutationMatrix σ

omit [Fintype V] in
lemma linearStep_zero (r : ℝ) (σ : Equiv.Perm V) : linearStep r σ 0=1 := by
  simp [linearStep]

lemma linearStep_substochastic (r : ℝ) (σ : Equiv.Perm V) (t : ℝ)
    (h0 : 0≤r*t) (h1 : r*t≤1) : DoublySubstochastic (linearStep r σ t) := by
  have hh:=weighted_average (V:=V) (fun b : Bool=>if b then 1-r*t else r*t)
    (fun b=>by cases b; exact h0; exact sub_nonneg.mpr h1)
    (by simp) (fun b : Bool=>if b then 1 else permutationMatrix σ)
    (fun b=>by cases b; exact permutationMatrix_substochastic σ; exact DoublySubstochastic.one)
  change DoublySubstochastic (fun i j=>(1-r*t)*(1:Matrix V V ℝ) i j+(r*t)*permutationMatrix σ i j)
  simpa only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false] using hh

include fV in
lemma linearStep_derivative (r : ℝ) (σ : Equiv.Perm V) :
    HasDerivAt (linearStep r σ) (r • (permutationMatrix σ-1)) 0 := by
  have hd:=(hasDerivAt_id (0:ℝ)).const_mul r
  have hh:=((hasDerivAt_const (0:ℝ) 1).sub hd |>.smul_const (1:Matrix V V ℝ)).add
    (hd.smul_const (permutationMatrix σ))
  convert hh using 1 <;> try dsimp [linearStep]
  all_goals try simp only [mul_one,zero_sub,smul_sub,neg_smul]
  all_goals first | rfl | abel

def linearMesh : List (Clock V) → ℝ → Matrix V V ℝ
  | [],_=>1
  | e::L,t=>linearStep e.1 e.2 t*linearMesh L t

lemma linearMesh_zero (L : List (Clock V)) : linearMesh L 0=1 := by
  induction L with
  | nil=>rfl
  | cons e L ih=>simp [linearMesh,linearStep_zero,ih]

lemma linearMesh_derivative (L : List (Clock V)) : HasDerivAt (linearMesh L) (clockGenerator L) 0 := by
  induction L with
  | nil=>exact hasDerivAt_const _ _
  | cons e L ih=>
    have hh:=(linearStep_derivative (e.1:ℝ) e.2).fun_mul ih
    change HasDerivAt (linearMesh (e::L)) _ _ at hh
    simpa only [clockGenerator,linearMesh_zero,linearStep_zero,mul_one,one_mul] using hh

lemma linearMesh_locally_substochastic (L : List (Clock V)) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → DoublySubstochastic (linearMesh L t) := by
  induction L with
  | nil=>exact Filter.Eventually.of_forall (fun _ _=>DoublySubstochastic.one)
  | cons e L ih=>
    have hh : ∀ᶠ t in 𝓝 (0:ℝ),(e.1:ℝ)*t≤1 := by
      have hc : ContinuousAt (fun t : ℝ=>(e.1:ℝ)*t) 0:=continuousAt_const.mul continuousAt_id
      exact (hc.eventually (eventually_le_nhds (by simp : (e.1:ℝ)*0<1)))
    filter_upwards [ih,hh] with t ht hrate
    intro h0
    exact (linearStep_substochastic _ _ _ (mul_nonneg e.1.property h0) hrate).mul (ht h0)

theorem linear_mesh_converges [Nonempty V] (L : List (Clock V)) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun n : ℕ=>(linearMesh L (t/(n+1:ℝ)))^(n+1)) atTop
      (𝓝 (NormedSpace.exp (t • clockGenerator L))) := by
  apply ExchangeLimit.local_contraction_product_limit _ _ (linearMesh_zero L) (linearMesh_derivative L)
    ?_ (fun u hu=>substochastic_norm_le (kernel_substochastic (clockGenerator_subMarkov L) hu)) t ht
  filter_upwards [linearMesh_locally_substochastic L] with u hu
  intro h0
  exact substochastic_norm_le (hu h0)

end Heisenberg.ExchangeMatrix
end
end
end

end OAI
