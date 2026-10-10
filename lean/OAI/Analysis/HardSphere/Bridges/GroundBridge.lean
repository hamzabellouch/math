import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeResidual
import OAI.Analysis.HardSphere.Geometry.GroundPathWeight

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener

lemma preserving_weighted {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {T : A→B} (hT : MeasurePreserving T μ ν)
    (f : B→ℝ≥0∞) (hf : Measurable f) :
    MeasurePreserving T (μ.withDensity (f∘T)) (ν.withDensity f) := by
  refine ⟨hT.measurable,?_⟩
  ext S hS
  rw [Measure.map_apply hT.measurable hS,withDensity_apply _ (hS.preimage hT.measurable),withDensity_apply _ hS]
  exact (hT.restrict_preimage hS).lintegral_comp hf

abbrev BridgeEndpoints (N : ℕ) (L : Length) := (Direction N→ℝ)×Configuration N L

def bridgeEndpointBase (N : ℕ) (L : Length) : Measure (BridgeEndpoints N L) :=
  (gaussianCoordinates N).prod volume

def endpointBridgePath (N : ℕ) (L : Length) (t : ℝ)
    (p : BridgeEndpoints N L×CoordinatePaths N) : ConfigurationPath N L :=
  freeTrajectory N L t (reconstructCoordinates N (p.1.1,p.2)) p.1.2

lemma endpointBridgePath_continuous (N : ℕ) (L : Length) (t : ℝ) :
    Continuous (endpointBridgePath N L t) := by
  exact (freeTrajectory_continuous N L t).comp
    (((reconstructCoordinates_continuous N).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)

lemma endpointBridgePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (endpointBridgePath N L t)
      ((bridgeEndpointBase N L).prod (coordinateBridge N)) (freePathLaw N L t) := by
  have h₁ := measurePreserving_prodAssoc (gaussianCoordinates N) (volume : Measure (Configuration N L)) (coordinateBridge N)
  have h₂ := (MeasurePreserving.id (gaussianCoordinates N)).prod
    (Measure.measurePreserving_swap (μ:=(volume : Measure (Configuration N L))) (ν:=coordinateBridge N))
  have h₃ := (measurePreserving_prodAssoc (gaussianCoordinates N) (coordinateBridge N) (volume : Measure (Configuration N L))).symm MeasurableEquiv.prodAssoc
  have h₄ := (reconstructCoordinates_preserving N).prod (MeasurePreserving.id (volume : Measure (Configuration N L)))
  have h₅ : MeasurePreserving (fun p : CoordinatePaths N×Configuration N L ↦ freeTrajectory N L t p.1 p.2)
      ((coordinateWiener N).prod volume) (freePathLaw N L t) := ⟨(freeTrajectory_continuous N L t).measurable,rfl⟩
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

def bridgeEnd (N : ℕ) (L : Length) (t : ℝ) (e : BridgeEndpoints N L) : Configuration N L :=
  fun i j ↦ e.2 i j+((Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)
lemma bridgeEnd_continuous (N : ℕ) (L : Length) (t : ℝ) : Continuous (bridgeEnd N L t) := by
  unfold bridgeEnd
  fun_prop

def endpointWeight {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) (e : BridgeEndpoints N L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 e.2‖*‖u.1 (bridgeEnd N L t e)‖))
lemma endpointWeight_measurable {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : Measurable (endpointWeight u t) := by
  unfold endpointWeight
  exact (measurable_const.mul (((Lp.stronglyMeasurable u.1).measurable.comp measurable_snd).norm.mul
    (((Lp.stronglyMeasurable u.1).measurable.comp (bridgeEnd_continuous N L t).measurable).norm))).ennreal_ofReal

lemma endpointBridge_weight {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) :
    (fun p : BridgeEndpoints N L×CoordinatePaths N ↦ endpointWeight u t p.1)=ᵐ[(bridgeEndpointBase N L).prod (coordinateBridge N)]
      fun p ↦ ENNReal.ofReal (groundPathWeight u t (endpointBridgePath N L t p)) := by
  have h : ∀ᵐ p : BridgeEndpoints N L×CoordinatePaths N ∂(bridgeEndpointBase N L).prod (coordinateBridge N),
      ∀j, p.2 j (0:Time)=0 ∧ p.2 j (1:Time)=0 :=
    (Measure.ae_prod_iff_ae_ae (by measurability)).mpr (ae_of_all _ (fun _ ↦ coordinateBridge_endpoints N))
  filter_upwards [h] with p hp
  have h0 : endpointBridgePath N L t p 0=p.1.2 := by
    ext i j
    change p.1.2 i j+((Real.sqrt (2*t)*(p.1.1 (i,j) • linearPath+p.2 (i,j)) 0:ℝ):AddCircle L.val)=p.1.2 i j
    simp [hp,linearPath]
  have h1 : endpointBridgePath N L t p 1=bridgeEnd N L t p.1 := by
    ext i j
    change p.1.2 i j+((Real.sqrt (2*t)*(p.1.1 (i,j) • linearPath+p.2 (i,j)) 1:ℝ):AddCircle L.val)=_
    simp [hp,linearPath,bridgeEnd]
  simp [endpointWeight,groundPathWeight,h0,h1]

def endpointInteraction (N : ℕ) (L : Length) (a t : ℝ) : Set (BridgeEndpoints N L×CoordinatePaths N) :=
  endpointBridgePath N L t ⁻¹' staysAllowed N L a
lemma endpointInteraction_measurable (N : ℕ) (L : Length) (a t : ℝ) : MeasurableSet (endpointInteraction N L a t) :=
  (staysAllowed_open N L a).measurableSet.preimage (endpointBridgePath_continuous N L t).measurable

def endpointWeightedBase {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : Measure (BridgeEndpoints N L) :=
  (bridgeEndpointBase N L).withDensity (endpointWeight u t)

lemma genuine_ground_bridge {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ) :
    (((endpointWeightedBase u t).prod (coordinateBridge N)).restrict (endpointInteraction N L a t)).map (endpointBridgePath N L t)=
      groundPathLaw N L a t u := by
  have hf := endpointBridgePath_preserving N L t
  have hw := preserving_weighted (hf.restrict_preimage (staysAllowed_open N L a).measurableSet)
    (fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω)) (groundPathWeight_measurable u t).ennreal_ofReal
  change _=(killedPathLaw N L a t).withDensity _
  rw [endpointWeightedBase,prod_withDensity_left (endpointWeight_measurable u t),restrict_withDensity (endpointInteraction_measurable N L a t)]
  have he : ((fun p : BridgeEndpoints N L×CoordinatePaths N ↦ endpointWeight u t p.1))=ᵐ[((bridgeEndpointBase N L).prod (coordinateBridge N)).restrict (endpointInteraction N L a t)]
      ((fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω))∘endpointBridgePath N L t) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le (endpointBridge_weight u t)
  rw [withDensity_congr_ae he]
  exact hw.map_eq

end HardSphere

end
end

end

end OAI
