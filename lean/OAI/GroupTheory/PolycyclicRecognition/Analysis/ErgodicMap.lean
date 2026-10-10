import Mathlib.Dynamics.Ergodic.Action.Basic

namespace OAI

/-! # Pushforward of an ergodic measure by an equivariant map -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction G X] [MulAction G Y] [MeasurableConstSMul G X] [MeasurableConstSMul G Y]

omit [MeasurableConstSMul G X] in
/-- An equivariant measurable factor of an ergodic action is ergodic. -/
theorem ergodicSMul_map (μ : Measure X) [ErgodicSMul G X μ]
    (f : X → Y) (hf : Measurable f) (heq : ∀ (g : G) x, f (g • x) = g • f x) :
    ErgodicSMul G Y (μ.map f) := by
  have hInv : SMulInvariantMeasure G Y (μ.map f) := by
    constructor
    intro g s hs
    rw [Measure.map_apply hf (hs.preimage (measurable_const_smul g)),
      Measure.map_apply hf hs]
    have hp : f ⁻¹' ((g • ·) ⁻¹' s) = (g • ·) ⁻¹' (f ⁻¹' s) := by
      ext x
      simp only [mem_preimage, heq]
    rw [hp, measure_preimage_smul]
  refine { toSMulInvariantMeasure := hInv, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro s hs hgs
  have hpre : ∀ g : G, (g • ·) ⁻¹' (f ⁻¹' s) =ᵐ[μ] f ⁻¹' s := by
    intro g
    filter_upwards [ae_of_ae_map hf.aemeasurable (hgs g)] with x hx
    change (f (g • x) ∈ s) = (f x ∈ s)
    change (g • f x ∈ s) = (f x ∈ s) at hx
    rwa [heq]
  have hconst := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
    (hs.preimage hf) hpre
  rcases eventuallyEmptyOrUniv_iff.mp hconst with h | h
  · exact eventuallyEmptyOrUniv_iff.mpr
      (Or.inl ((ae_map_iff hf.aemeasurable hs).mpr h))
  · exact eventuallyEmptyOrUniv_iff.mpr
      (Or.inr ((ae_map_iff hf.aemeasurable hs.compl).mpr h))

end PolycyclicRecognition

end OAI
