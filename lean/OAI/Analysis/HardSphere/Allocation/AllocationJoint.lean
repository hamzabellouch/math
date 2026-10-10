import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridAllocation

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def GroupWeak {N : ℕ} (m G : ℕ) (g : Fin G) (B : Finset (Fin N))
    (a : Allocation (G*(2*m)) (Fin N)) : Prop :=
  ∃f,a=some f ∧ m≤(Finset.univ.filter (fun k ↦ f (groupPosition (2*m) G g k)∈B)).card

lemma allocation_group_weak {N : ℕ} (E B : Finset (Fin N)) (m G : ℕ) (g : Fin G)
    (hE : G*(2*m)≤E.card) (hB : 10*(E∩B).card≤E.card) :
    (allocationPMF E (G*(2*m))).toMeasure {a | GroupWeak m G g B a}≤
      ENNReal.ofReal ((2/5:ℝ)^m) := by
  let f : Allocation (G*(2*m)) (Fin N)→Allocation (2*m) (Fin N) :=
    Option.map (fun a ↦ (groupPosition (2*m) G g).trans a)
  have hf : Measurable f := measurable_of_countable _
  have hmap : ((allocationPMF E (G*(2*m))).toMeasure).map f=(allocationPMF E (2*m)).toMeasure := by
    rw [PMF.toMeasure_map _ _ hf,allocated_group_uniform E _ _ hE]
  have hsub : {a | GroupWeak m G g B a}⊆f ⁻¹' {a | ∃b,a=some b ∧ m≤(Finset.univ.filter (fun k ↦ b k∈B)).card} := by
    rintro a ⟨b,rfl,hb⟩
    exact ⟨_,rfl,hb⟩
  have hm : 2*m≤E.card := (show 2*m≤G*(2*m) by
    have hg : 1≤G := Nat.succ_le_iff.mpr (Nat.zero_le g.val |>.trans_lt g.isLt)
    simpa using Nat.mul_le_mul_right (2*m) hg).trans hE
  apply (measure_mono hsub).trans
  rw [←Measure.map_apply hf (by exact MeasurableSet.of_discrete),hmap]
  exact allocation_half_bad E B m hm hB

lemma grid_group_joint_weak {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) (m G : ℕ) (g : Fin G)
    (B : (Fin 3→Fin K)→Finset (Fin N)) (A : Finset (Fin 3→Fin K))
    (hE : ∀v∈A,G*(2*m)≤(recordedList hL v p).card)
    (hB : ∀v∈A,10*((recordedList hL v p)∩B v).card≤(recordedList hL v p).card) :
    gridAllocationKernel hL (G*(2*m)) p {a | ∀v∈A,GroupWeak m G g (B v) (a v)}≤
      (ENNReal.ofReal ((2/5:ℝ)^m))^A.card := by
  rw [gridAllocationKernel_apply]
  rw [show (Measure.pi (fun v ↦ (allocationPMF (recordedList hL v p) (G*(2*m))).toMeasure))
      {a | ∀v∈A,GroupWeak m G g (B v) (a v)} =
      ∏v∈A,(allocationPMF (recordedList hL v p) (G*(2*m))).toMeasure {a | GroupWeak m G g (B v) a} from
    pi_failure_sets _ (fun v ↦ {a | GroupWeak m G g (B v) a}) A]
  calc
    _ ≤ ∏v∈A,ENNReal.ofReal ((2/5:ℝ)^m) := Finset.prod_le_prod (fun v hv ↦
      allocation_group_weak _ _ m G g (hE v hv) (hB v hv))
    _ = _ := by simp

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff Comparison CellOrbital

lemma endpointEligible_unique {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {v w : Fin 3→Fin K} {s₀ : ℝ} {Y Z : Configuration N L} {i : Fin N}
    (hv : EndpointEligible v s₀ Y Z i) (hw : EndpointEligible w s₀ Y Z i) : v=w := by
  by_contra h
  exact Set.disjoint_left.mp (centeredCell_disjoint hL hK h) hv.1 hw.1

lemma ownEligible_at {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (e : BridgeEndpoints N L) (β : Bridge.Noise) (v : Fin 3→Fin K)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L t e) i) :
    ownEligible (K:=K) m r R C S s₀ t u i (e,β) ↔
      Regular m r R C u S (projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β)) ∧
      Confined (gridCenter L v) (projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β)) := by
  have hp : ownPath i t (e,β)=projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β) := by
    exact labelBridgePath_lift t e (fun _ ↦ β) i
  unfold ownEligible
  rw [hp]
  constructor
  · rintro ⟨w,hw,hreg,hconf⟩
    have hh := endpointEligible_unique hL hK he hw
    subst w
    exact ⟨hreg,hconf⟩
  · rintro ⟨hreg,hconf⟩
    exact ⟨v,he,hreg,hconf⟩

lemma near_anchor_lift {L : Length} (hL : 1≤L.val) (y : Point) (v : Torus L)
    (hy : projectPoint L y∈centeredCell L v) :
    ∃c : Point,projectPoint L c=v ∧ ‖y-c‖≤1/2 := by
  have hm := (centeredCell_image hL v (projectPoint L y)).mp hy
  choose s hs he using hm
  refine ⟨fun j ↦ y j-s j,?_,?_⟩
  · funext j
    change ((y j-s j:ℝ):AddCircle L.val)=v j
    rw [AddCircle.coe_sub,he j]
    change ((y j:ℝ):AddCircle L.val)-(((y j:ℝ):AddCircle L.val)-v j)=v j
    abel
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
    intro j
    change |y j-(y j-s j)|≤1/2
    rw [sub_sub_cancel]
    exact abs_le.mpr ⟨by linarith [(hs j).1],(hs j).2.le⟩

end HardSphere.Groups

end
end

end

end OAI
