import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Operators.ScalarMultiplierCommutation
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem shiftOperator_ae (ξ : Hilbert) :
    shiftOperator ξ =ᵐ[baseMeasure] fun x => WeightedShift.shift 1 (ξ x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem multiplier_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (ξ : Hilbert) :
    multiplier θ g C hC hg hb ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.diagonal (multiplierField θ g C hb x) (ξ x) := by
  unfold multiplier
  exact WeightedShift.fieldDiagonal_ae _ _ _ _ _ _

theorem shiftOperator_commutes_multiplier (g : Lp ℂ ∞ baseMeasure) :
    Commute shiftOperator (L2Multiplication.multiplier (E := Fiber) g) :=
  L2Multiplication.commute_multiplier_of_represented shiftOperator
    (fun _ => (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap)
    shiftOperator_ae g

theorem multiplier_commutes_scalar (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (a : Lp ℂ ∞ baseMeasure) :
    Commute (multiplier θ g C hC hg hb) (L2Multiplication.multiplier (E := Fiber) a) :=
  L2Multiplication.commute_multiplier_of_represented _
    (fun x => WeightedShift.diagonal (multiplierField θ g C hb x))
    (multiplier_ae θ g C hC hg hb) a

theorem scalarMultiplier_mem_commutant (θ : ℕ → ℝ) (g : Lp ℂ ∞ baseMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (factor θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  have hcomm : ∀ a : Lp ℂ ∞ baseMeasure,
      Commute A (L2Multiplication.multiplier (E := Fiber) a) := by
    rcases hA with hA | hA
    · rcases Set.mem_singleton_iff.mp hA with rfl
      exact shiftOperator_commutes_multiplier
    · obtain ⟨f, C, hC, hf, hb, rfl⟩ := hA
      exact multiplier_commutes_scalar θ f C hC hf hb
  exact ⟨(hcomm g).eq, (L2Multiplication.star_commutes_multiplier A hcomm g).eq⟩

theorem factor_commutes_scalarMultiplier (θ : ℕ → ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (g : Lp ℂ ∞ baseMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) :=
  (VonNeumannAlgebra.mem_commutant_iff.mp (scalarMultiplier_mem_commutant θ g)) T hT

theorem exists_unique_field {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Base → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => G x (ξ x)) →
          F =ᵐ[baseMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (factor_commutes_scalarMultiplier θ hT)

end Invariant233.ProductModel

end

end OAI
