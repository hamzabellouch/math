import OAI.Analysis.KadisonSimilarity.Representation.FiniteSymmetrization
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Integrability of the scalar matrix coefficients of an operator field. -/
def WeaklyIntegrable (A : X → H →L[ℂ] H) : Prop :=
  ∀ x y : H, Integrable (fun g => inner ℂ (A g x) y) μ

private def integralOperatorForm (A : X → H →L[ℂ] H) : H → H → ℂ :=
  fun x y => ∫ g, inner ℂ (A g x) y ∂μ

omit [CompleteSpace H] [IsProbabilityMeasure μ] in
private theorem isOperatorForm_integral (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) : IsOperatorForm (integralOperatorForm μ A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    simp only [integralOperatorForm, map_add, inner_add_left]
    exact integral_add (hA x z) (hA y z)
  · intro c x y
    simp only [integralOperatorForm, map_smul, inner_smul_left]
    exact integral_const_mul (star c) _
  · intro x y z
    simp only [integralOperatorForm, inner_add_right]
    exact integral_add (hA x y) (hA x z)
  · intro c x y
    simp only [integralOperatorForm, inner_smul_right]
    exact integral_const_mul c _

omit [CompleteSpace H] in
private theorem norm_integralOperatorForm_le (A : X → H →L[ℂ] H) {R : ℝ}
    (hA : ∀ g, ‖A g‖ ≤ R) (x y : H) :
    ‖integralOperatorForm μ A x y‖ ≤ R * ‖x‖ * ‖y‖ := by
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ (A g x) y‖ ≤ R * ‖x‖ * ‖y‖ :=
    Filter.Eventually.of_forall fun g => calc
      _ ≤ ‖A g x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖A g‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((A g).le_opNorm x) (norm_nonneg y)
      _ ≤ R * ‖x‖ * ‖y‖ := by gcongr; exact hA g
  simpa only [integralOperatorForm, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- The weak integral of a uniformly bounded, weakly integrable field. -/
def weakOperatorIntegral (A : X → H →L[ℂ] H) (hA : WeaklyIntegrable μ A)
    (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R) : H →L[ℂ] H :=
  operatorOfForm (integralOperatorForm μ A) (isOperatorForm_integral μ A hA) R
    (norm_integralOperatorForm_le μ A hbound)

@[simp] theorem weakOperatorIntegral_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R) (x y : H) :
    inner ℂ (weakOperatorIntegral μ A hA R hbound x) y =
      ∫ g, inner ℂ (A g x) y ∂μ := operatorOfForm_inner ..

theorem norm_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ g, ‖A g‖ ≤ R) :
    ‖weakOperatorIntegral μ A hA R hbound‖ ≤ R :=
  norm_operatorOfForm_le _ _ R hR _

/-- Left and right multiplication may be passed through the weak integral. -/
theorem weakOperatorIntegral_sandwich_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B C : H →L[ℂ] H) (x y : H) :
    inner ℂ ((B * weakOperatorIntegral μ A hA R hbound * C) x) y =
      ∫ g, inner ℂ ((B * A g * C) x) y ∂μ := by
  change inner ℂ (B (weakOperatorIntegral μ A hA R hbound (C x))) y = _
  rw [← adjoint_inner_right, weakOperatorIntegral_inner]
  apply integral_congr_ae
  filter_upwards with g
  exact adjoint_inner_right B (A g (C x)) y

/-- A commutator with a fixed operator may be passed through the weak integral. -/
theorem weakOperatorIntegral_commutator_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) (x y : H) :
    inner ℂ (commutator (weakOperatorIntegral μ A hA R hbound) B x) y =
      ∫ g, inner ℂ (commutator (A g) B x) y ∂μ := by
  simp only [commutator, sub_apply, ContinuousLinearMap.mul_def, comp_apply, inner_sub_left]
  rw [weakOperatorIntegral_inner, ← adjoint_inner_right, weakOperatorIntegral_inner,
    ← integral_sub (hA (B x) y) (hA x (B.adjoint y))]
  apply integral_congr_ae
  filter_upwards with g
  rw [adjoint_inner_right]

/-- Uniform commutator bounds are preserved by weak integration. -/
theorem norm_commutator_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ g, ‖commutator (A g) B‖ ≤ c) :
    ‖commutator (weakOperatorIntegral μ A hA R hbound) B‖ ≤ c := by
  apply norm_le_of_matrix_coefficients _ hc
  intro x y
  rw [← norm_inner_symm, weakOperatorIntegral_commutator_inner]
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ (commutator (A g) B x) y‖ ≤ c * ‖x‖ * ‖y‖ :=
    Filter.Eventually.of_forall fun g => calc
      _ ≤ ‖commutator (A g) B x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖commutator (A g) B‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((commutator (A g) B).le_opNorm x) (norm_nonneg y)
      _ ≤ c * ‖x‖ * ‖y‖ := by gcongr; exact hcomm g
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [probReal_univ, mul_one] at hi
  convert hi using 1
  ring

end KadisonSimilarity

end

end OAI
