import OAI.Analysis.IrrationalRotation.Rotation.PositiveDiagonalFields
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields
import OAI.Analysis.IrrationalRotation.Analysis.FieldCovariance

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Invariant233.DirectIntegral

variable {Y E ι : Type*} [MeasurableSpace Y] {μ : Measure Y}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Countable ι]

theorem ae_invariant_of_represented_invariant
    (b : HilbertBasis ι ℂ E)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p W : Y → E →L[ℂ] E)
    (hP : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun y => W y (ξ y))
    (hinv : (1 - P) * T * P = 0) :
    ∀ᵐ y ∂μ, (1 - p y) * W y * p y = 0 := by
  apply L2Multiplication.field_unique_of_representation b
    ((1 - P) * T * P) (fun y => (1 - p y) * W y * p y) (fun _ => 0)
  · intro ξ
    filter_upwards [hP ξ, hT (P ξ), hP (T (P ξ)),
      Lp.coeFn_sub (T (P ξ)) (P (T (P ξ)))] with y hp ht hpp hsub
    change ((T (P ξ) - P (T (P ξ))) y) =
      W y (p y (ξ y)) - p y (W y (p y (ξ y)))
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [ht, hpp, ht, hp]
  · intro ξ
    rw [hinv]
    filter_upwards [Lp.coeFn_zero E 2 μ] with y hy
    exact hy

variable [CompleteSpace E]

theorem ae_isStarProjection_of_representation
    (b : HilbertBasis ι ℂ E)
    (P : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p : Y → E →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖p y‖ ≤ C)
    (hm : ∀ v, StronglyMeasurable fun y => p y v)
    (hrep : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hP : IsStarProjection P) : ∀ᵐ y ∂μ, IsStarProjection (p y) := by
  let := L2Multiplication.separableSpace_of_countable_hilbertBasis b
  have heq : P = fieldOperator p C hbound (fun v => (hm v).aestronglyMeasurable) := by
    ext ξ
    exact (hrep ξ).trans (fieldOperator_ae p C hbound
      (fun v => (hm v).aestronglyMeasurable) ξ).symm
  apply ae_isStarProjection_of_fieldOperator b hC hm
  rw [← heq]
  exact hP

omit [CompleteSpace E] in

theorem real_constant_vector_state_eq_integral
    (P : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p : Y → E →L[ℂ] E)
    (hrep : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y)) (e : E) :
    (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re =
      ∫ y, (inner ℂ e (p y e)).re ∂μ := by
  have hi : Integrable (fun y => inner ℂ e (p y e)) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (Lp.const 2 μ e)
      (P (Lp.const 2 μ e))).congr
    filter_upwards [Lp.coeFn_const 2 μ e, hrep (Lp.const 2 μ e)] with y he hp
    rw [hp, he]
    rfl
  rw [FieldTraceCyclic.constant_vector_state_eq_integral P p hrep e]
  exact (integral_re hi).symm

end Invariant233.DirectIntegral

namespace Invariant233.Fields

variable {Y E ι : Type*} [MeasurableSpace Y] {μ : Measure Y}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Countable ι]

theorem ae_strict_diagonal_of_represented_weighted_shift
    (b : HilbertBasis ι ℂ E) {σ : Y → Y} (hσ : Ergodic σ μ)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p D : Y → E →L[ℂ] E)
    (S : (E →L[ℂ] E)ˣ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, ‖p y‖ ≤ C)
    (hm : ∀ v, StronglyMeasurable fun y => p y v)
    (hp : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun y =>
      ((S : E →L[ℂ] E) * D y) (ξ y))
    (hP : IsStarProjection P) (hinv : (1 - P) * T * P = 0)
    (hcov : ∀ᵐ y ∂μ, p (σ y) = ↑(S⁻¹) * p y * (S : E →L[ℂ] E))
    {e : E} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hmean0 : 0 < (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re)
    (hmean1 : (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re < 1) :
    ∀ᵐ y ∂μ, 0 < (inner ℂ e (p y e)).re ∧ (inner ℂ e (p y e)).re < 1 := by
  have hproj := DirectIntegral.ae_isStarProjection_of_representation
    b P p C hC hbound hm hp hP
  have hfield := DirectIntegral.ae_invariant_of_represented_invariant
    b P T p (fun y => (S : E →L[ℂ] E) * D y) hp hT hinv
  have hreal := DirectIntegral.real_constant_vector_state_eq_integral P p hp e
  apply ae_strict_projection_diagonal_of_weighted_shift hσ S he hproj hD hf heigen
    hcov hfield
  · exact ((Complex.continuous_re.comp
      (continuous_const.inner continuous_id)).comp_stronglyMeasurable (hm e)).measurable
  · rwa [← hreal]
  · rwa [← hreal]

end Invariant233.Fields

end

end OAI
