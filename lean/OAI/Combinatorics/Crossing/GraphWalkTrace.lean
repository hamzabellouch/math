import OAI.Combinatorics.Crossing.EmbeddedGraphPaths
import OAI.Combinatorics.Crossing.UniqueWalkPassage

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_piece_subset_range (v : ℕ → Plane) :
    (k : ℕ) → ∀ i, i < k → segment ℝ (v i) (v (i+1)) ⊆ Set.range (polygonalArcPath v k)
  | 0, i, hi => by omega
  | 1, i, hi => by
    have he : i=0 := by omega
    subst i
    rw [polygonalArcPath,Path.range_segment]
  | k+2, i, hi => by
    rw [polygonalArcPath,Path.trans_range]
    by_cases hin : i < k+1
    · exact (polygonalArcPath_piece_subset_range v (k+1) i hin).trans Set.subset_union_left
    · have he : i=k+1 := by omega
      subst i
      rw [Path.range_segment]
      exact Set.subset_union_right

theorem graphWalkPath_dart_subset_range {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    segment ℝ (pos d.fst) (pos d.snd) ⊆ Set.range (graphWalkPath pos p) := by
  obtain ⟨i,hi,hfst,hsnd⟩ := walk_dart_parameters p d hd
  rw [hfst,hsnd]
  exact polygonalArcPath_piece_subset_range (fun i => pos (p.getVert i)) p.length i hi

theorem walk_dart_at {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (i : ℕ) (hi : i < p.length) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  have hi' : i < p.darts.length := by simpa only [p.length_darts] using hi
  refine ⟨p.darts[i],List.getElem_mem hi',?_,?_⟩
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]

theorem graphWalkPath_range_subset_of_darts_subset {V : Type*} {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p q : G.Walk a b) (hd : q.darts ⊆ p.darts) :
    Set.range (graphWalkPath pos q) ⊆ Set.range (graphWalkPath pos p) := by
  intro x hx
  by_cases hq : q.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (q.getVert i)) q.length) at hx
    rw [hq] at hx
    obtain ⟨t,ht⟩ := hx
    have he : x=pos a := by simpa [polygonalArcPath,q.getVert_zero] using ht.symm
    exact ⟨0,(graphWalkPath pos p).source.trans he.symm⟩
  · obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (fun i => pos (q.getVert i)) q.length (by omega) x hx
    obtain ⟨d,hdq,hfst,hsnd⟩ := walk_dart_at q i hi
    apply graphWalkPath_dart_subset_range pos p d (hd hdq)
    simpa only [hfst,hsnd] using hxi

theorem graphWalkPath_bypass_range_subset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Set.range (graphWalkPath pos p.bypass) ⊆ Set.range (graphWalkPath pos p) :=
  graphWalkPath_range_subset_of_darts_subset pos p p.bypass p.darts_bypass_subset_darts

end Zarankiewicz

end

end OAI
