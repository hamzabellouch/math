import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.Transfer

theorem half_sum_abs_le_sqrt_card_mul_sqrt_sum_sq
    {α : Type*} [Fintype α] (f : α → ℝ) :
    (1 / 2 : ℝ) * ∑ a, |f a| ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.sqrt (∑ a, (f a) ^ 2) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := Finset.univ) (f := fun _ : α => (1 : ℝ)) (g := fun a => |f a|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hsum : 0 ≤ ∑ a, |f a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsq : 0 ≤ ∑ a, (f a) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcard : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hsqrt : (Real.sqrt (Fintype.card α : ℝ) *
      Real.sqrt (∑ a, (f a) ^ 2)) ^ 2 =
      (Fintype.card α : ℝ) * ∑ a, (f a) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard, Real.sq_sqrt hsq]
  have hnonneg : 0 ≤ Real.sqrt (Fintype.card α : ℝ) *
      Real.sqrt (∑ a, (f a) ^ 2) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

theorem half_sum_abs_le_sqrt_card_mul_exp
    {α : Type*} [Fintype α] (f : α → ℝ) (r : ℝ)
    (h : ∑ a, (f a) ^ 2 ≤ Real.exp (-2 * r)) :
    (1 / 2 : ℝ) * ∑ a, |f a| ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-r) := by
  have hexp : Real.exp (-2 * r) = (Real.exp (-r)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrt : Real.sqrt (∑ a, (f a) ^ 2) ≤ Real.exp (-r) := by
    rw [hexp] at h
    exact (Real.sqrt_le_left (Real.exp_nonneg _)).2 h
  exact (half_sum_abs_le_sqrt_card_mul_sqrt_sum_sq f).trans
    (mul_le_mul_of_nonneg_left hsqrt (div_nonneg (Real.sqrt_nonneg _) (by norm_num)))

theorem norm_sq_map_le_of_positive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : E →ₗ[ℝ] E) (hP : P.IsPositive)
    (q : ℝ)
    (hbound : ∀ x : E, inner ℝ (P x) x ≤ q * ‖x‖ ^ 2) (x : E) :
    ‖P x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := by
  classical
  let b := hP.isSymmetric.eigenvectorBasis rfl
  have heig (i : Fin (Module.finrank ℝ E)) :
      hP.isSymmetric.eigenvalues rfl i ≤ q := by
    have hb := hbound (b i)
    simpa only [b, hP.isSymmetric.apply_eigenvectorBasis,
      inner_smul_real_left, real_inner_self_eq_norm_sq, smul_eq_mul,
      OrthonormalBasis.norm_eq_one, one_pow, mul_one] using hb
  rw [← b.repr.norm_map (P x), ← b.repr.norm_map x,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change ((hP.isSymmetric.eigenvectorBasis rfl).repr (P x) i) ^ 2 ≤
    q ^ 2 * ((hP.isSymmetric.eigenvectorBasis rfl).repr x i) ^ 2
  rw [hP.isSymmetric.eigenvectorBasis_apply_self_apply, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (hP.nonneg_eigenvalues rfl i) (heig i) 2

theorem norm_sq_map_le_of_poincare
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : E →ₗ[ℝ] E) (hP : P.IsPositive)
    (W : Submodule ℝ E) (hW : ∀ x ∈ W, P x ∈ W)
    (γ : ℝ) (hgap : ∀ x ∈ W, γ * ‖x‖ ^ 2 ≤ inner ℝ x (x - P x))
    (x : E) (hx : x ∈ W) :
    ‖P x‖ ^ 2 ≤ (1 - γ) ^ 2 * ‖x‖ ^ 2 := by
  let Q : W →ₗ[ℝ] W := P.restrict hW
  have hQ : Q.IsPositive := ⟨hP.isSymmetric.restrict_invariant hW, fun y => hP.2 y⟩
  have hbound (y : W) : inner ℝ (Q y) y ≤ (1 - γ) * ‖y‖ ^ 2 := by
    have hg := hgap y y.property
    rw [inner_sub_right, real_inner_self_eq_norm_sq, ← real_inner_comm y.val (P y.val)] at hg
    change inner ℝ (P y.val) y.val ≤ (1 - γ) * ‖y.val‖ ^ 2
    nlinarith
  exact norm_sq_map_le_of_positive Q hQ (1 - γ) hbound ⟨x, hx⟩

theorem half_sum_abs_le_exp_of_sq_contraction
    {α : Type*} [Fintype α] (f : ℕ → α → ℝ) (γ : ℝ) (hγ : γ ≤ 1)
    (hzero : ∑ a, (f 0 a) ^ 2 ≤ 1)
    (hstep : ∀ t, ∑ a, (f (t + 1) a) ^ 2 ≤
      (1 - γ) ^ 2 * ∑ a, (f t a) ^ 2) (t : ℕ) :
    (1 / 2 : ℝ) * ∑ a, |f t a| ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-γ * t) := by
  have hbase : (1 - γ) ^ 2 ≤ Real.exp (-2 * γ) := by
    have he := Real.add_one_le_exp (-γ)
    have hp : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
    have hle : 1 - γ ≤ Real.exp (-γ) := by linarith
    calc
      (1 - γ) ^ 2 ≤ (Real.exp (-γ)) ^ 2 := pow_le_pow_left₀ hp hle 2
      _ = Real.exp (-2 * γ) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hdecay : ∀ t : ℕ, ∑ a, (f t a) ^ 2 ≤ Real.exp (-2 * (γ * t)) := by
    intro t
    induction t with
    | zero => simpa using hzero
    | succ t ih =>
      calc
        ∑ a, (f (t + 1) a) ^ 2 ≤ (1 - γ) ^ 2 * ∑ a, (f t a) ^ 2 := hstep t
        _ ≤ Real.exp (-2 * γ) * Real.exp (-2 * (γ * t)) :=
          mul_le_mul hbase ih (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
            (Real.exp_nonneg _)
        _ = Real.exp (-2 * (γ * (t + 1 : ℕ))) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
  simpa only [neg_mul] using half_sum_abs_le_sqrt_card_mul_exp (f t) (γ * t) (hdecay t)

end Problem315.Transfer

end

end OAI
