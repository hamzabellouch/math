import Mathlib
import OAI.Analysis.HardSphere.Comparison.FiberNormalize
import OAI.Analysis.HardSphere.Conditioning.RouteObservation

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal
namespace HardSphere.Comparison

lemma fiberNormalize_supported {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)} (hC : MeasurableSet C) (w : W) :
    ∀ᵐ v ∂fiberNormalize κ C w,(w,v)∈C := by
  change ∀ᵐ v ∂(fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w,(w,v)∈C
  apply Measure.smul_absolutelyContinuous.ae_le
  rw [fiberRestrict_apply κ hC]
  exact ae_restrict_mem (hC.preimage (measurable_const.prodMk measurable_id))

def commonLaw {E P W : Type*} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace W]
    (d : ℕ) (ξ : Measure W) [SFinite ξ]
    (τ : Measure (Fin (d+2) → E×(P×P))) [IsFiniteMeasure τ]
    (C : Set (W×(Fin (d+2) → E×(P×P)))) : Measure (W×(Fin (d+2) → E×(P×P))) :=
  ξ.compProd (fiberNormalize (Kernel.const W τ) C)

lemma commonLaw_environment {E P W : Type*} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace W]
    (d : ℕ) (ξ : Measure W) [SFinite ξ]
    (τ : Measure (Fin (d+2) → E×(P×P))) [IsFiniteMeasure τ]
    {C : Set (W×(Fin (d+2) → E×(P×P)))} (hC : MeasurableSet C)
    (hpos : ∀ᵐ w ∂ξ,0<τ {v | (w,v)∈C}) : (commonLaw d ξ τ C).map Prod.fst=ξ :=
  fiberNormalize_fst ξ (Kernel.const W τ) hC hpos

lemma commonLaw_probability {E P W : Type*} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace W]
    (d : ℕ) (ξ : Measure W) [IsProbabilityMeasure ξ]
    (τ : Measure (Fin (d+2) → E×(P×P))) [IsFiniteMeasure τ]
    {C : Set (W×(Fin (d+2) → E×(P×P)))} (hC : MeasurableSet C)
    (hpos : ∀ᵐ w ∂ξ,0<τ {v | (w,v)∈C}) : IsProbabilityMeasure (commonLaw d ξ τ C) :=
  ⟨fiberNormalize_compProd_mass ξ (Kernel.const W τ) hC hpos⟩

lemma commonLaw_sameObservation {E P W : Type*} [MeasurableSpace E] [MeasurableEq E]
    [MeasurableSpace P] [MeasurableSpace W] (d : ℕ) (π : P→E) (hπ : Measurable π)
    (ξ : Measure W) [SFinite ξ]
    (τ : Measure (Fin (d+2) → E×(P×P))) [IsFiniteMeasure τ]
    (hτ : ∀ᵐ v ∂τ,∀k,π (v k).2.1=(v k).1 ∧ π (v k).2.2=(v k).1)
    {C : Set (W×(Fin (d+2) → E×(P×P)))} (hC : MeasurableSet C) :
    (commonLaw d ξ τ C).map (fun p ↦ observeFirst d π p.swap)=
    (commonLaw d ξ τ C).map (fun p ↦ observeSecond d π p.swap) := by
  apply Measure.map_congr
  have h : ∀ᵐ p ∂commonLaw d ξ τ C,∀k,π (p.2 k).2.1=(p.2 k).1 ∧ π (p.2 k).2.2=(p.2 k).1 := by
    rw [commonLaw,Measure.ae_compProd_iff (by measurability)]
    exact ae_of_all _ (fun w ↦ (fiberNormalize_ac (Kernel.const W τ) hC w).ae_le hτ)
  filter_upwards [h] with p hp
  exact observations_eq d π p.2 p.1 hp

end HardSphere.Comparison

end
end

end

end OAI
