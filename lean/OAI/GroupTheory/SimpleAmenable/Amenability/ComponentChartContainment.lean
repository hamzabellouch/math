import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierSignalSystem
import OAI.GroupTheory.SimpleAmenable.Amenability.ChartLineTransport
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ChartBoundaryEndpoints

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ComponentChartContainment
open Classical Set

theorem barrier_component_cut_ordinary {a : ℕ} {B : Set (ℝ×ℝ)} {j : Fin 4} {c : CutRing}
    (hline : ∀x ∈ squareInterior,cutForm a j x=ordinary c → x ∈ B)
    {p x : ℝ×ℝ} (hp : p ∈ barrierRegion B)
    (hx : x ∈ connectedComponentIn (barrierRegion B) p) :
    cutForm a j x ≠ ordinary c ∧ (cutForm a j x < ordinary c ↔ cutForm a j p < ordinary c) := by
  have hn (y : ℝ×ℝ) (hy : y ∈ connectedComponentIn (barrierRegion B) p) : cutForm a j y ≠ ordinary c := by
    intro he
    have hr := connectedComponentIn_subset (barrierRegion B) p hy
    exact hr.2 (hline y hr.1 he)
  refine ⟨hn x hx,?_⟩
  have hh := continuous_nonzero_sign isPreconnected_connectedComponentIn
    ((cutForm_continuous a j).sub continuous_const).continuousOn
    (fun y hy => sub_ne_zero.mpr (hn y hy)) hx (mem_connectedComponentIn hp)
  simpa only [Pi.sub_apply,sub_lt_zero] using hh

theorem barrier_component_openChart {a : ℕ} {B : Set (ℝ×ℝ)}
    (T : Finset PlaneCut) (p : GenericSquare a)
    (hp : p.val ∈ barrierRegion B)
    (hline : ∀l ∈ T,∀x ∈ squareInterior,cutForm a l.1 x=ordinary l.2 → x ∈ B) :
    connectedComponentIn (barrierRegion B) p.val ⊆ openSquareChart T p := by
  intro x hx
  refine ⟨(connectedComponentIn_subset (barrierRegion B) p.val hx).1,?_⟩
  intro l
  obtain ⟨hne,hs⟩ := barrier_component_cut_ordinary (hline l.val l.property) hp hx
  by_cases hh : cutForm a l.val.1 p.val < ordinary l.val.2
  · simpa [squareSign,hh] using hs.mpr hh
  · simpa [squareSign,hh] using lt_of_le_of_ne (le_of_not_gt (fun h => hh (hs.mp h))) hne.symm

theorem barrier_component_translatedChart {a : ℕ} {B : Set (ℝ×ℝ)}
    (T : Finset PlaneCut) (p q : GenericSquare a) (u : CutRing×CutRing)
    (hqp : q.val=p.val+(ordinary u.1,ordinary u.2))
    (hq : q.val ∈ barrierRegion B)
    (hline : ∀l ∈ T ∪ squareBoundaryCuts,∀x ∈ squareInterior,
      cutForm a l.1 x=ordinary (l.2+integralCutForm a l.1 u) → x ∈ B) :
    ∀x ∈ connectedComponentIn (barrierRegion B) q.val,
      x-(ordinary u.1,ordinary u.2) ∈ openSquareChart T p := by
  intro x hx
  have hsign (l : PlaneCut) (hl : l ∈ T ∪ squareBoundaryCuts) :
      cutForm a l.1 (x-(ordinary u.1,ordinary u.2)) ≠ ordinary l.2 ∧
      (cutForm a l.1 (x-(ordinary u.1,ordinary u.2)) < ordinary l.2 ↔
        cutForm a l.1 p.val < ordinary l.2) := by
    obtain ⟨hne,hs⟩ := barrier_component_cut_ordinary (hline l hl) hq hx
    rw [hqp,cutForm_add,cutForm_ordinary,map_add] at hs
    rw [map_add] at hne
    rw [cutForm_sub,cutForm_ordinary]
    refine ⟨fun h => hne (by linarith),?_⟩
    constructor
    · intro h
      have hh := hs.mp (by linarith : cutForm a l.1 x < ordinary l.2+ordinary (integralCutForm a l.1 u))
      linarith
    · intro h
      have hh := hs.mpr (by linarith : cutForm a l.1 p.val+ordinary (integralCutForm a l.1 u) < ordinary l.2+ordinary (integralCutForm a l.1 u))
      linarith
  have hp := generic_mem_squareInterior p
  have hx₀ := hsign (0,0) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hx₁ := hsign (0,1) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hy₀ := hsign (1,0) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hy₁ := hsign (1,1) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  simp only [cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_zero,map_one,Prod.fst_sub,Prod.snd_sub] at hx₀ hx₁ hy₀ hy₁
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => not_lt_of_gt hp.1.1 (hx₀.2.mp h))) hx₀.1.symm
  · exact hx₁.2.mpr hp.1.2
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => not_lt_of_gt hp.2.1 (hy₀.2.mp h))) hy₀.1.symm
  · exact hy₁.2.mpr hp.2.2
  · intro l
    obtain ⟨hne,hs⟩ := hsign l.val (Finset.mem_union_left _ l.property)
    by_cases hh : cutForm a l.val.1 p.val < ordinary l.val.2
    · simpa [squareSign,hh] using hs.mpr hh
    · simpa [squareSign,hh] using lt_of_le_of_ne (le_of_not_gt (fun h => hh (hs.mp h))) hne.symm

end ComponentChartContainment

section ComponentTransport
open Classical Set
namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem component_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p q : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hqp : q.val=p.val+(ordinary u.1,ordinary u.2))
    (hQ : 0 ≤ Q) (huQ : ∀j,|conjugate (integralCutForm a j u)| ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (hQN : Q < N) (hBN : B ≤ N)
    (b₁ b₂ b₁' b₂' : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs' : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁' j))
    (ht : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    (ht' : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂' j))
    (hb₁ : ∀j z,b₁' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ j z)
    (hb₂ : ∀j z,b₂' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ j z) :
    (fun x => x+(ordinary u.1,ordinary u.2)) '' connectedComponentIn
      (barrierRegion (sampledBarriers ha i N
        (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂)) p.val =
    connectedComponentIn (barrierRegion (sampledBarriers ha k N
      (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂')) q.val := by
  let v := (ordinary u.1,ordinary u.2)
  let A₀ := sampledBarriers ha i N
    (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂
  let A₁ := sampledBarriers ha k N
    (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂'
  have hp : p.val ∈ barrierRegion A₀ := generic_mem_barrierRegion (sampledBarriers_supported ha i N _ b₂) p
  have hq : q.val ∈ barrierRegion A₁ := generic_mem_barrierRegion (sampledBarriers_supported ha k N _ b₂') q
  have hsource : connectedComponentIn (barrierRegion A₀) p.val ⊆ openSquareChart T p := by
    apply barrier_component_openChart T p hp
    intro l hl x hx hxc
    have hband := ((hB l (Finset.mem_union_left _ hl)).1).trans hBN
    exact S.central_line_barrier i hN b₁ b₂ hs ht
      ⟨by linarith, x,hx,hxc⟩ hband x hx hxc
  have htarget : ∀x ∈ connectedComponentIn (barrierRegion A₁) q.val,x-v ∈ openSquareChart T p := by
    apply barrier_component_translatedChart T p q u hqp hq
    intro l hl x hx hxc
    have hband := ((hB l hl).2).trans hBN
    exact S.central_line_barrier k hN b₁' b₂' hs' ht'
      ⟨by linarith,x,hx,hxc⟩ hband x hx hxc
  have hbar (x : ℝ×ℝ) (hx : x ∈ openSquareChart T p) : x ∈ A₀ ↔ x+v ∈ A₁ :=
    S.chart_barrier_transport g i k T hT p u hdata hQ huQ hB hN hQN
      b₁ b₂ b₁' b₂' hs hs' ht ht' hb₁ hb₂ hx
  have hforward : (fun x => x+v) '' connectedComponentIn (barrierRegion A₀) p.val ⊆
      connectedComponentIn (barrierRegion A₁) q.val := by
    apply (isPreconnected_connectedComponentIn.image _ (continuous_id.add continuous_const).continuousOn).subset_connectedComponentIn
    · exact ⟨p.val,mem_connectedComponentIn hp,hqp.symm⟩
    · rintro x ⟨y,hy,rfl⟩
      have hyC := hsource hy
      have hyreg := connectedComponentIn_subset (barrierRegion A₀) p.val hy
      refine ⟨?_,fun h => hyreg.2 ((hbar y hyC).mpr h)⟩
      have himage := fullGroupAffineChart_square g i T hT p
      rw [hdata] at himage
      exact himage ⟨y,hyC,rfl⟩
  have hbackward : (fun x => x-v) '' connectedComponentIn (barrierRegion A₁) q.val ⊆
      connectedComponentIn (barrierRegion A₀) p.val := by
    apply (isPreconnected_connectedComponentIn.image _ (continuous_id.sub continuous_const).continuousOn).subset_connectedComponentIn
    · refine ⟨q.val,mem_connectedComponentIn hq,?_⟩
      change q.val-v=p.val
      rw [hqp,add_sub_cancel_right]
    · rintro x ⟨y,hy,rfl⟩
      have hyC := htarget y hy
      have hyreg := connectedComponentIn_subset (barrierRegion A₁) q.val hy
      refine ⟨hyC.1,?_⟩
      intro h
      have hh := (hbar (y-v) hyC).mp h
      rw [sub_add_cancel] at hh
      exact hyreg.2 hh
  apply Subset.antisymm hforward
  intro y hy
  exact ⟨y-v,hbackward ⟨y,hy,rfl⟩,sub_add_cancel y v⟩

end BarrierSignalSystem
end ComponentTransport

end SimpleAmenable
end
end

end OAI
