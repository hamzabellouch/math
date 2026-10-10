import Mathlib
import OAI.Analysis.HardSphere.Bridges.ExposedReference
import OAI.Analysis.HardSphere.Comparison.ParameterTarget

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]
  [MeasurableSpace.CountableOrCountablyGenerated E C(Time,Point)]

lemma accessible_physical_auxiliary
    {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (B : Set Point) (hB : MeasurableSet B) (hBvol : volume B=1)
    (hb : ∀e u,u∈B → ‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hs : ∀e,ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B)
      {u | ENNReal.ofReal (9/10:ℝ)≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S)})
    (ht' : ∀e,ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B)
      {u | ENNReal.ofReal (9/10:ℝ)≤trialKernel t (y' e) (z' e) u (Prod.mk e ⁻¹' T)}) :
    let A := commonAccessible (parameterTrialKernel t y z hy hz) (parameterTrialKernel t y' z' hy' hz')
      (exposedSuccess S) (exposedSuccess T) (ENNReal.ofReal (9/10:ℝ)) (ENNReal.ofReal (9/10:ℝ)) B
    ∃ hA : MeasurableSet A, ∃κ : Kernel (E×C(Time,Point)) (Point×C(Time,Point)), IsFiniteKernel κ ∧
      (parameterIndividualReference t y z hy hz S hS).compProd κ=
        exposedPairedTrialKernel (parameterTargetKernel (by rw [hBvol]; exact ENNReal.one_ne_top) A hA)
          t y z y' z' hy hz hy' hz' S T hS hT ∧
      (∀e f,κ (e,f) univ ≤ (ENNReal.ofReal (9/10:ℝ))⁻¹*
        ((ENNReal.ofReal (49/50:ℝ))⁻¹*(midpointLower t C)⁻¹)) ∧
      (∀e,∫⁻f,κ (e,f) univ ∂parameterIndividualReference t y z hy hz S hS e=1) := by
  dsimp only
  let A := commonAccessible (parameterTrialKernel t y z hy hz) (parameterTrialKernel t y' z' hy' hz')
    (exposedSuccess S) (exposedSuccess T) (ENNReal.ofReal (9/10:ℝ)) (ENNReal.ofReal (9/10:ℝ)) B
  have hA : MeasurableSet A := commonAccessible_measurable _ _ _ _
    (exposedSuccess_measurable hS) (exposedSuccess_measurable hT) _ _ _ hB
  have hAB (e : E) : Prod.mk e ⁻¹' A ⊆ B := fun _ hu ↦ hu.1.2
  have hAf (e : E) : volume (Prod.mk e ⁻¹' A)≠⊤ :=
    ne_top_of_le_ne_top (by rw [hBvol]; exact ENNReal.one_ne_top) (measure_mono (hAB e))
  have hvol (e : E) : ENNReal.ofReal (49/50:ℝ)≤volume (Prod.mk e ⁻¹' A) := by
    apply commonAccessible_volume volume _ _ _ _ (exposedSuccess_measurable hS)
      (exposedSuccess_measurable hT) _ _ B hB hBvol e
    · simpa only [accessibleTarget,Set.preimage_ofPred_eq,parameterTrialKernel_apply,exposedSuccess,Set.preimage_preimage] using hs e
    · simpa only [accessibleTarget,Set.preimage_ofPred_eq,parameterTrialKernel_apply,exposedSuccess,Set.preimage_preimage] using ht' e
  have haa (e : E) : ∀ᵐu ∂targetUniform (Prod.mk e ⁻¹' A), u∈Prod.mk e ⁻¹' A :=
    Measure.ae_smul_measure (ae_restrict_mem (hA.preimage measurable_prodMk_left)) _
  refine ⟨hA,?_⟩
  apply exposed_physical_auxiliary _ ht hC y z y' z' hy hz hy' hz' S T hS hT
    (fun e ↦ Prod.mk e ⁻¹' A) (fun _ ↦ hA.preimage measurable_prodMk_left) hAf
    (parameterTargetKernel_apply _ A hA hAB) (a:=ENNReal.ofReal (49/50:ℝ))
    (c:=ENNReal.ofReal (9/10:ℝ)) (by norm_num) (by norm_num) hvol
  · exact fun e u hu ↦ hb e u (hAB e hu)
  · intro e
    filter_upwards [haa e] with u hu
    simpa only [accessibleTarget,Set.mem_ofPred_eq,parameterTrialKernel_apply,exposedSuccess,Set.preimage_preimage] using hu.2.1
  · intro e
    filter_upwards [haa e] with u hu
    apply lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ))
    simpa only [accessibleTarget,Set.mem_ofPred_eq,parameterTrialKernel_apply,exposedSuccess,Set.preimage_preimage] using hu.2.2

end HardSphere.Bridge

end
end

end

end OAI
