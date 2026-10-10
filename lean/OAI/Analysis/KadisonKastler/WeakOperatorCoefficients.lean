import OAI.Analysis.KadisonKastler.WeakOperatorFields
import OAI.Analysis.KadisonKastler.ScalarOperatorKernel
import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable

namespace OAI

/-! # Scalar coefficients determine weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- A representative is the one-element case of a uniformly bounded family. -/
def asUniformFamily (F : WeakOperatorRepresentative (H := H) μ) :
    UniformMeasurableOperators Unit D H μ where
  eval _ := eval F
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le _ := eval_norm_le F
  measurable _ := eval_aestronglyMeasurable F

/-- Scalar matrix coefficients as L-infinity classes. -/
def coefficient (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) : ScalarLInfinity μ :=
  (asUniformFamily F).coefficient () ξ η

omit [IsFiniteMeasure μ] in
theorem coefficient_ae (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient F ξ η =ᵐ[μ] fun x => inner ℂ η (eval F x ξ) :=
  (asUniformFamily F).coefficient_ae () ξ η

/-- The bounded sesquilinear kernel of a representative. -/
def scalarKernel (F : WeakOperatorRepresentative (H := H) μ) : ScalarOperatorKernel H μ where
  coeff := coefficient F
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le := (asUniformFamily F).norm_coefficient_le ()
  add_left := (asUniformFamily F).coefficient_add_left ()
  add_right := (asUniformFamily F).coefficient_add_right ()
  smul_left := (asUniformFamily F).coefficient_smul_left ()
  smul_right := (asUniformFamily F).coefficient_smul_right ()

omit [IsFiniteMeasure μ] in
/-- Almost-everywhere equal representatives have identical scalar coefficients. -/
theorem coefficient_eq_of_ae (F G : WeakOperatorRepresentative (H := H) μ)
    (h : eval F =ᵐ[μ] eval G) (ξ η : H) : coefficient F ξ η = coefficient G ξ η := by
  apply Lp.ext
  filter_upwards [coefficient_ae F ξ η, coefficient_ae G ξ η, h] with x hF hG hFG
  rw [hF, hG, hFG]

omit [IsFiniteMeasure μ] in
/-- Conversely, a countable dense set of coefficients detects AE equality. -/
theorem ae_eq_of_coefficient_eq [TopologicalSpace.SeparableSpace H]
    (F G : WeakOperatorRepresentative (H := H) μ)
    (h : ∀ ξ η : H, coefficient F ξ η = coefficient G ξ η) : eval F =ᵐ[μ] eval G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hp (i j : ℕ) : ∀ᵐ x ∂μ,
      inner ℂ (v i) (eval F x (v j)) = inner ℂ (v i) (eval G x (v j)) := by
    have hi := h (v j) (v i)
    filter_upwards [coefficient_ae F (v j) (v i), coefficient_ae G (v j) (v i)] with x hF hG
    rw [hi] at hF
    exact hF.symm.trans hG
  have hall : ∀ᵐ x ∂μ, ∀ i j : ℕ,
      inner ℂ (v i) (eval F x (v j)) = inner ℂ (v i) (eval G x (v j)) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hp i j
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  have he : (fun ξ => eval F x ξ) = (fun ξ => eval G x ξ) := by
    apply hv.equalizer (eval F x).continuous (eval G x).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => hx i j)
  exact congrFun he

omit [IsFiniteMeasure μ] in
/-- Scalar coefficients exactly detect equality in the actual C-star quotient. -/
theorem quotient_eq_iff_coefficient_eq [TopologicalSpace.SeparableSpace H]
    (F G : WeakOperatorRepresentative (H := H) μ) :
    operatorFieldQuotient μ F = operatorFieldQuotient μ G ↔
      ∀ ξ η : H, coefficient F ξ η = coefficient G ξ η := by
  rw [operatorFieldQuotient_eq_iff]
  exact ⟨fun h ξ η => coefficient_eq_of_ae F G h ξ η,
    ae_eq_of_coefficient_eq F G⟩

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
