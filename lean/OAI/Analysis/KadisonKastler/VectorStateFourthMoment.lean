import OAI.Analysis.KadisonKastler.MatrixStateMoments
import OAI.Analysis.KadisonKastler.FiniteSignFourthMoment

namespace OAI

/-! # Nontracial fourth moments of independent signs

The three-pairing sign identity holds for the actual vector functional.
The crossed pairing is bounded after summing the two orders of its
indices. This avoids applying a tracial fourth-moment theorem to the
nontracial vector state in the modular graph argument.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real part of the ambient vector state, as a real-linear functional. -/
def realVectorState (Ω : H) : (H →L[ℂ] H) →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((operatorVectorState Ω).restrictScalars ℝ)

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
@[simp] theorem realVectorState_apply (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω x = (inner ℂ Ω (x Ω)).re := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity of the vector functional is a Hilbert norm identity. -/
theorem realVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω (star x * x) = ‖x Ω‖ ^ 2 := by
  simp only [realVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

omit [DecidableEq ι] in
private theorem sign_fourth_integrand (Ω : H)
    (a : ι → H →L[ℂ] H) (ε : ι → Bool) :
    realVectorState Ω ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          realVectorState Ω ((star (a i) * a j) * (star (a k) * a l)) := by
  have hprod : star (finiteSignSum a ε) * finiteSignSum a ε =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) • (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  rw [hprod, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Exact three-pairing expansion in an arbitrary vector state. The
third pairing stays in its original order; no trace cycling is used. -/
theorem expect_finiteSignSum_vector_fourth (Ω : H) (a : ι → H →L[ℂ] H) :
    (𝔼 ε : ι → Bool,
      realVectorState Ω ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) =
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a i) * (star (a j) * a j))) +
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) ^ 2)) +
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i))) -
      2 * ∑ i, realVectorState Ω ((star (a i) * a i) ^ 2) := by
  simp_rw [sign_fourth_integrand]
  simpa only [pow_two] using expect_finiteSign_four_sum
    (fun i j k l => realVectorState Ω ((star (a i) * a j) * (star (a k) * a l)))

omit [DecidableEq ι] in
/-- Summing both index orders bounds the crossed pairing by the positive
pairing, even though the state is not tracial. -/
theorem sum_vectorState_crossed_le (Ω : H) (a : ι → H →L[ℂ] H) :
    (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) ^ 2)) ≤
      ∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) := by
  have hp (i j : ι) :
      2 * realVectorState Ω ((star (a i) * a j) ^ 2) ≤
        realVectorState Ω ((star (a j) * a i) * (star (a i) * a j)) +
        realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) := by
    have h := operatorVectorState_square_re_le Ω (star (a i) * a j)
    have h₁ := realVectorState_star_mul_self Ω (star (a i) * a j)
    have h₂ := realVectorState_star_mul_self Ω (star (a j) * a i)
    simp only [star_mul, star_star] at h₁ h₂ h
    change 2 * realVectorState Ω ((star (a i) * a j) ^ 2) ≤ _ at h
    rw [← h₁, ← h₂] at h
    exact h
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hp i j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have hswap :
      (∑ i, ∑ j, realVectorState Ω ((star (a j) * a i) * (star (a i) * a j))) =
      ∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) :=
    Finset.sum_comm
  rw [hswap] at hs
  linarith

/-- The nontracial sign fourth moment is controlled by its two positive
pairings. This is the estimate needed before averaging the matrix orbits. -/
theorem expect_finiteSignSum_vector_fourth_le (Ω : H) (a : ι → H →L[ℂ] H) :
    (𝔼 ε : ι → Bool,
      realVectorState Ω ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) ≤
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a i) * (star (a j) * a j))) +
      2 * (∑ i, ∑ j,
        realVectorState Ω ((star (a i) * a j) * (star (a j) * a i))) := by
  rw [expect_finiteSignSum_vector_fourth]
  have hcross := sum_vectorState_crossed_le Ω a
  have hdiag : 0 ≤ ∑ i, realVectorState Ω ((star (a i) * a i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    have he : (star (a i) * a i) ^ 2 =
        star (star (a i) * a i) * (star (a i) * a i) := by
      simp only [star_mul, star_star, pow_two]
    rw [he, realVectorState_star_mul_self]
    exact sq_nonneg _
  linarith

end

end KadisonKastler

end OAI
