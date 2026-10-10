import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierChartRefinement
import OAI.GroupTheory.SimpleAmenable.Amenability.LocalBarrierTransport
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ChartBoundaryEndpoints

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ChartLineTransport
open Classical Set
namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem chart_line_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hQ : 0 ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (j : Fin 4) (c : CutRing)
    (hc : c ∈ barrierCandidate a j N)
    (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
    (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
    (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
    (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
    (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
    {x : ℝ} (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    x ∈ subdivisionBarrier (barrierSubdivision ha i j c
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁)) (barrierActivation ha i j c b₂) ↔
    x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u)
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁'))
        (barrierActivation ha k j (c+integralCutForm a j u) b₂') := by
  let d := barrierLineParameter j (ordinary u.1,ordinary u.2)
  obtain ⟨L,U,hxLU,hL,hU,hchart,hend⟩ := chart_line_endpoints_forced T p hc hx
  have hLU : L < U := hxLU.1.trans hxLU.2
  have htrans : ∀r ∈ Ioo L U,barrierLinePoint a j (c+integralCutForm a j u) (r+d) ∈ squareInterior := by
    intro r hr
    rw [barrierLinePoint_translate]
    have hh := fullGroupAffineChart_square g i T hT p
    rw [hdata] at hh
    exact hh ⟨barrierLinePoint a j c r,hchart r hr,rfl⟩
  have hbounds := interval_endpoints_closed (continuous_id.add continuous_const)
    isClosed_Icc hLU (fun r hr => let hp := (barrierLinePoint_interior_iff hc' (r+d)).mp (htrans r hr)
      show r+d ∈ Icc (barrierLineLower a j (c+integralCutForm a j u))
        (barrierLineUpper a j (c+integralCutForm a j u)) from ⟨hp.1.le,hp.2.le⟩)
  have hsource (r : ℝ) (hr : r ∈ ({L,U} : Finset ℝ))
      (hrb : r ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c)) :
      r ∈ barrierSubdivision ha i j c (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁) := by
    obtain ⟨l,hl,hjl,hzero⟩ := hend r hr
    exact S.crossing_in_subdivision i hN hjl hc (by linarith [hc.1]) (hB l hl).1 b₁ hs hrb hzero
  have htarget (r : ℝ) (hr : r ∈ ({L,U} : Finset ℝ))
      (hrb : r+d ∈ Icc (barrierLineLower a j (c+integralCutForm a j u))
        (barrierLineUpper a j (c+integralCutForm a j u))) :
      r+d ∈ barrierSubdivision ha k j (c+integralCutForm a j u)
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁') := by
    obtain ⟨l,hl,hjl,hzero⟩ := hend r hr
    apply S.crossing_in_subdivision k hN hjl hc' (by linarith [hc'.1]) (hB l hl).2 b₁' hs' hrb
    rw [barrierLinePoint_translate,cutForm_add,hzero,cutForm_ordinary,map_add]
  apply S.local_line_transport g i k (lt_of_lt_of_le zero_lt_one hN) j c u hc hc' b₁ b₂ b₁' b₂'
    hs hs' hb₁ hb₂ L U (fun r hr => ⟨(hchart r hr).1,htrans r hr⟩) hU.2
    (hsource L (by simp) hL) (hsource U (by simp) hU)
    (htarget L (by simp) hbounds.1) (htarget U (by simp) hbounds.2) _ hxLU
  intro r hr z hzi hzp
  exact (flagAffineData_barrier_chart ha g i j c T hT p hLU hr
    (fun l hl r hr => openSquareChart_signs (hchart r hr) hl) z.val.2 hzp).trans hdata

end BarrierSignalSystem
end ChartLineTransport

section ChartBarrierTransport
open Classical Set

theorem mem_sampledBarriers_iff {a m : ℕ} (ha : 0 < a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (p : ℝ×ℝ) : p ∈ sampledBarriers ha i N M b ↔
      ∃j c,c ∈ barrierCandidate a j N ∧ cutForm a j p=ordinary c ∧
        barrierLineParameter j p ∈ subdivisionBarrier (barrierSubdivision ha i j c (M j))
          (barrierActivation ha i j c (b j)) := by
  constructor
  · rintro ⟨⟨j,c,hc⟩,st,hst,x,hx,rfl⟩
    refine ⟨j,c,hc,cutForm_barrierLinePoint a j c x,?_⟩
    rw [barrierLineParameter_point]
    exact (mem_barrierActiveIntervals_image_iff ha i j c (M j) (b j) x).mp ⟨st,hst,hx⟩
  · rintro ⟨j,c,hc,hpc,hp⟩
    obtain ⟨st,hst,hx⟩ := (mem_barrierActiveIntervals_image_iff ha i j c (M j) (b j) _).mpr hp
    exact ⟨⟨j,⟨c,hc⟩⟩,st,hst,barrierLineParameter j p,hx,barrierLinePoint_parameter hpc⟩

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem active_line_small {m : ℕ} (i : Fin m) {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (c : CutRing) (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal (S.second j).signal N) b)
    {x : ℝ} (hx : x ∈ subdivisionBarrier (barrierSubdivision ha i j c M) (barrierActivation ha i j c b)) :
    |conjugate c| < 3*N := by
  by_contra hn
  have he := secondSignal_negative_empty ha i hN hc M (S.second j).signal b
    (S.second_neg j) hs (le_of_not_gt hn)
  obtain ⟨st,hst,_⟩ := (mem_barrierActiveIntervals_image_iff ha i j c M b x).mpr hx
  rw [he] at hst
  exact Finset.notMem_empty st hst

theorem chart_barrier_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hQ : 0 ≤ Q) (huQ : ∀j,|conjugate (integralCutForm a j u)| ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (hQN : Q < N)
    (b₁ b₂ b₁' b₂' : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs' : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁' j))
    (ht : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    (ht' : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂' j))
    (hb₁ : ∀j z,b₁' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ j z)
    (hb₂ : ∀j z,b₂' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ j z)
    {x : ℝ×ℝ} (hx : x ∈ openSquareChart T p) :
    x ∈ sampledBarriers ha i N (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂ ↔
    x+(ordinary u.1,ordinary u.2) ∈ sampledBarriers ha k N
      (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂' := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hx' : x+(ordinary u.1,ordinary u.2) ∈ squareInterior := by
    have hh := fullGroupAffineChart_square g i T hT p
    rw [hdata] at hh
    exact hh ⟨x,hx,rfl⟩
  rw [mem_sampledBarriers_iff,mem_sampledBarriers_iff]
  constructor
  · rintro ⟨j,c,hc,hline,hactive⟩
    have hsmall := S.active_line_small i hN₀ j c hc _ (b₂ j) (ht j) hactive
    have hc' : c+integralCutForm a j u ∈ barrierCandidate a j N := by
      refine ⟨?_,x+(ordinary u.1,ordinary u.2),hx',?_⟩
      · rw [map_add]
        calc
          |conjugate c+conjugate (integralCutForm a j u)| ≤ |conjugate c|+|conjugate (integralCutForm a j u)| := abs_add_le _ _
          _ ≤ 4*N := by linarith [huQ j]
      · rw [cutForm_add,hline,cutForm_ordinary,map_add]
    have hxline : barrierLinePoint a j c (barrierLineParameter j x) ∈ openSquareChart T p := by
      rwa [barrierLinePoint_parameter hline]
    have htransport := S.chart_line_transport g i k T hT p u hdata hQ hB hN j c hc hc'
      (b₁ j) (b₂ j) (b₁' j) (b₂' j) (hs j) (hs' j) (hb₁ j) (hb₂ j) hxline
    refine ⟨j,c+integralCutForm a j u,hc',?_,?_⟩
    · rw [cutForm_add,hline,cutForm_ordinary,map_add]
    · rw [barrierLineParameter_add]
      exact htransport.mp hactive
  · rintro ⟨j,c',hc',hline',hactive'⟩
    let c := c'-integralCutForm a j u
    have hce : c+integralCutForm a j u=c' := sub_add_cancel _ _
    have hline : cutForm a j x=ordinary c := by
      rw [cutForm_add,cutForm_ordinary] at hline'
      dsimp [c]
      rw [map_sub]
      linarith
    have hsmall := S.active_line_small k hN₀ j c' hc' _ (b₂' j) (ht' j) hactive'
    have hc : c ∈ barrierCandidate a j N := by
      refine ⟨?_,x,hx.1,hline⟩
      change |conjugate (c'-integralCutForm a j u)| ≤ _
      rw [map_sub]
      calc
        |conjugate c'-conjugate (integralCutForm a j u)| ≤ |conjugate c'|+|conjugate (integralCutForm a j u)| := abs_sub _ _
        _ ≤ 4*N := by linarith [huQ j]
    have hxline : barrierLinePoint a j c (barrierLineParameter j x) ∈ openSquareChart T p := by
      rwa [barrierLinePoint_parameter hline]
    have htransport := S.chart_line_transport g i k T hT p u hdata hQ hB hN j c hc
      (hce.symm ▸ hc') (b₁ j) (b₂ j) (b₁' j) (b₂' j) (hs j) (hs' j) (hb₁ j) (hb₂ j) hxline
    rw [hce] at htransport
    refine ⟨j,c,hc,hline,htransport.mpr ?_⟩
    simpa only [barrierLineParameter_add] using hactive'

end BarrierSignalSystem
end ChartBarrierTransport

end SimpleAmenable
end
end

end OAI
