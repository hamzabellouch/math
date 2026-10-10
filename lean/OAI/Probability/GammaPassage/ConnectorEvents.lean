import OAI.Probability.GammaPassage.BallTravel
import OAI.Probability.GammaPassage.CrossingLocalized

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge
open GammaFPP.IntervalTravelBridge Set MeasureTheory Filter
open scoped Topology

def allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : Set (Edge → ℝ) :=
  {w | ∀ p ∈ I, ∀ q ∈ J, w ∈ boundedLocalizedEvent V
    (fun a ds => a=p ∧ a+displacement ds=q) (fun _ _ => bound p q)}

theorem mem_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) (w : Edge → ℝ) :
    w ∈ allPairsRegionEvent V I J bound ↔
      ∀ p ∈ I, ∀ q ∈ J, ∃ ds, p+displacement ds=q ∧
        PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p q := by
  simp [allPairsRegionEvent,boundedLocalizedEvent]

theorem measurableSet_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : MeasurableSet (allPairsRegionEvent V I J bound) := by
  simp only [allPairsRegionEvent,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
      measurableSet_boundedLocalizedEvent V _ _))))

theorem allPairsRegionEvent_depends (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) :
    DependsOnEdges (allPairsRegionEvent V I J bound) (internalEdges V) := by
  intro w w' hh
  simp only [allPairsRegionEvent,mem_ofPred_eq]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  exact boundedLocalizedEvent_depends V _ _ w w' hh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- Uniform connection estimates for finite-region endpoint tests from
diameter, support-cost, and tube-containment bounds. -/
theorem gamma_allPairsRegionEvent (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ (V : Finset Vertex) (I J : Set Vertex)
      (bound : Vertex → Vertex → ℝ),
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      (∀ p ∈ I, ∀ q ∈ J, gammaMeanNorm h hshape hrate (latticeEmbed (q-p))+η*s ≤ bound p q) →
      (∀ p ∈ I, ∀ q ∈ J, SegmentTube p q (δ*s) ⊆ (V : Set Vertex)) →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [gamma_set_travel h hshape hrate D η δ hD hη hδ ε hε] with s hs
  intro V I J bound hdiam hcost hregion
  refine (measureReal_mono (show {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} ⊆
    {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel (gammaMeanNorm h hshape hrate) η δ s p q (fun e => τ e ω)} from ?_)).trans_lt
      (hs I J hdiam)
  intro ω hbad htravel
  apply hbad
  rw [mem_allPairsRegionEvent]
  intro p hp q hq
  obtain ⟨ds,hd,hc,hin⟩ := htravel p hp q hq
  refine ⟨ds,hd,?_,hc.trans (hcost p hp q hq)⟩
  intro i hi
  exact hregion p hp q hq (hin i hi)

end GammaFPP.CrossingBridge

end OAI
