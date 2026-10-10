import Mathlib
import OAI.Analysis.HardSphere.Bridges.ConfinedLift
import OAI.Analysis.HardSphere.Conditioning.ConditionTransport
import OAI.Analysis.HardSphere.Allocation.AllocationJoint

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def frozenPaths {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L)
    (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise) : {i // ¬p i} → ConfigurationPath 1 L :=
  fun j ↦ projectCurve L (leg t (labelStartLift e j) (labelEndLift t e j) (w j))

lemma actual_reference_event {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (b : Fin N→Bool) (i : {i // p i}) (hbi : b i=true)
    (v : Fin 3→Fin K) (vLift : Point)
    (hvLift : projectPoint L vLift=gridCenter L v)
    (hy : ‖labelStartLift e i-vLift‖≤3)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L (2*t) e) i) :
    individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i
      =ᵐ[Bridge.law]
    (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))⁻¹'
      permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
        vLift (frozenPaths (2*t) e p w) := by
  filter_upwards [leg_endpoints_ae (2*t) (labelStartLift e i) (labelEndLift (2*t) e i)] with β hβ
  apply propext
  have hown := ownEligible_at hL hK m r R C S s₀ (2*t) u i e β v he
  change (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u i (e,β)=b i ∧
    ∀j : {j // ¬p j},noisePairAvoid r (2*t) e i j β (w j) ∧ noisePairAvoid r (2*t) e j i (w j) β) ↔ _
  rw [hbi]
  simp only [eligibilityFlag,decide_eq_true_eq,hown]
  constructor
  · rintro ⟨⟨hreg,hconf⟩,havoid⟩
    refine ⟨hreg,?_,hβ,?_⟩
    · apply confined_lift h50 vLift _ (by simpa only [hβ.1] using hy)
      intro s
      rw [hvLift]
      exact hconf s
    · intro j
      exact (havoid j).1
  · rintro ⟨hreg,hconf,_,havoid⟩
    refine ⟨⟨hreg,?_⟩,?_⟩
    · intro s
      rw [←hvLift]
      exact (hconf s).2
    · intro j
      refine ⟨havoid j,?_⟩
      exact fun h ↦ havoid j ((physicalPairCheck_symmetric r _ _).mp h)

lemma actual_individual_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (b : Fin N→Bool) (i : {i // p i}) (hbi : b i=true)
    (v : Fin 3→Fin K) (vLift : Point)
    (hvLift : projectPoint L vLift=gridCenter L v)
    (hy : ‖labelStartLift e i-vLift‖≤3)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L (2*t) e) i) :
    (conditionedMeasure Bridge.law (individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)).map
      (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))=
    individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
      (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
        vLift (frozenPaths (2*t) e p w)) := by
  exact noise_reference_identification t _ _ _ (permittedPath_measurable ..)
    (actual_reference_event hL hK h50 m r R C S s₀ t u e p w b i hbi v vLift hvLift hy he)

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def physicalMutual {I : Type*} {L : Length} (r : ℝ) : Set (I → C(Time,Point)) :=
  pairEvent (fun _ _ f g ↦ ¬TrialCollision (L:=L) r (projectCurve L g) f)

lemma physicalMutual_measurable {I : Type*} [Fintype I] {L : Length} (r : ℝ) :
    MeasurableSet (physicalMutual (I:=I) (L:=L) r) :=
  pairEvent_measurable _ (fun _ _ ↦ (jointCollision_closed (L:=L) r).measurableSet.compl)

lemma physical_product_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N → Prop) (w : {i // ¬p i} → Bridge.Noise)
    (b : Fin N → Bool) (hbi : ∀i : {i // p i},b i=true)
    (v : {i // p i} → Fin 3 → Fin K) (vLift : {i // p i} → Point)
    (hvLift : ∀i,projectPoint L (vLift i)=gridCenter L (v i))
    (hy : ∀i : {i // p i},‖labelStartLift e i-vLift i‖≤3)
    (he : ∀i : {i // p i},EndpointEligible (v i) s₀ e.2 (bridgeEnd N L (2*t) e) i)
    (hnormal : ∀i : {i // p i},Bridge.law
      (individualFiber p (noisePairAvoid r (2*t) e)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)≠0) :
    (conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      conditionedMeasure Bridge.law (individualFiber p (noisePairAvoid r (2*t) e)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i))
      (pairEvent (fun i j : {i // p i} ↦ noisePairAvoid r (2*t) e i j))).map
      (fun β (i : {i // p i}) ↦ leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i) (β i))=
    conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (vLift i) (frozenPaths (2*t) e p w))) (physicalMutual (L:=L) r) := by
  let μ := fun i : {i // p i} ↦ conditionedMeasure Bridge.law
    (individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)
  let : ∀i,IsProbabilityMeasure (μ i) := fun i ↦ conditioned_probability Bridge.law (hnormal i)
  have hh := conditioned_pi_map μ
    (fun i ↦ leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))
    (fun i ↦ (leg_continuous ..).measurable) (physicalMutual_measurable (I:={i // p i}) (L:=L) r)
  have hm : ∀i,(μ i).map (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))=
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (vLift i) (frozenPaths (2*t) e p w)) := fun i ↦
    actual_individual_reference hL hK h50 m r R C S s₀ t u e p w b i (hbi i)
      (v i) (vLift i) (hvLift i) (hy i) (he i)
  simp_rw [hm] at hh
  exact hh

lemma physical_recorded_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool) (hbi : ∀i : {i // p i},b i=true) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ∀(v : {i // p i} → Fin 3 → Fin K) (vLift : {i // p i} → Point),
      (∀i,projectPoint L (vLift i)=gridCenter L (v i)) →
      (∀i : {i // p i},‖labelStartLift w.1 i-vLift i‖≤3) →
      (∀i : {i // p i},EndpointEligible (v i) s₀ w.1.2 (bridgeEnd N L (2*t) w.1) i) →
      (conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
        {β | blockGlue p (w,β)∈labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b}).map
        (fun β (i : {i // p i}) ↦ leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))=
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        individualReference t (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
          (permittedPath m r R C S u (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
            (vLift i) (frozenPaths (2*t) w.1 p w.2))) (physicalMutual (L:=L) r) := by
  filter_upwards [recorded_physical_fiber μ r (2*t)
    (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u)
    (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b p] with w hw
  intro v vLift hv hy he
  rw [hw.2.2]
  exact physical_product_reference hL hK h50 m r R C S s₀ t u w.1 p w.2 b hbi v vLift hv hy he hw.2.1

end HardSphere.Groups

end
end

end

end OAI
