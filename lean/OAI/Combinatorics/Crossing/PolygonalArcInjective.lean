import OAI.Combinatorics.Crossing.MinimumChainGeometry
import OAI.Combinatorics.Crossing.PathConcatenationInjective

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_range_piece (v : ℕ → Plane) :
    (n : ℕ) → 0 < n → ∀ x ∈ Set.range (polygonalArcPath v n),
      ∃ i, i < n ∧ x ∈ segment ℝ (v i) (v (i+1))
  | 0, hn, _, _ => by omega
  | 1, _, x, hx => by
    refine ⟨0,by omega,?_⟩
    simpa only [polygonalArcPath,Path.range_segment] using hx
  | n+2, _, x, hx => by
    rw [polygonalArcPath,Path.trans_range] at hx
    rcases hx with hx | hx
    · obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      exact ⟨i,by omega,hh⟩
    · exact ⟨n+1,by omega,by simpa only [Path.range_segment] using hx⟩

theorem polygonalArcPath_injective (v : ℕ → Plane) : (n : ℕ) → 0 < n →
    (∀ i, i < n → v i ≠ v (i+1)) →
    (∀ i j, i < j → j < n → ∀ x,
      x ∈ segment ℝ (v i) (v (i+1)) → x ∈ segment ℝ (v j) (v (j+1)) →
      j=i+1 ∧ x=v j) → Function.Injective (polygonalArcPath v n)
  | 0, hn, _, _ => by omega
  | 1, _, hn, _ => Path.segment_injective_of_ne (hn 0 (by omega))
  | n+2, _, hn, hm => by
    apply path_trans_injective
    · exact polygonalArcPath_injective v (n+1) (by omega)
        (fun i hi => hn i (by omega)) (fun i j hij hj => hm i j hij (by omega))
    · exact Path.segment_injective_of_ne (hn (n+1) (by omega))
    · intro x hx hy
      obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      rw [Path.range_segment] at hy
      exact (hm i (n+1) hi (by omega) x hh hy).2

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_path_injective (P : PolygonalChain O a b) (hab : a ≠ b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) : Function.Injective P.path := by
  have hp : 0 < P.pieces := by
    by_contra h
    have hz : P.pieces=0 := by omega
    exact hab (P.first.symm.trans (hz ▸ P.last))
  change Function.Injective (polygonalArcPath P.vertices P.pieces)
  apply polygonalArcPath_injective P.vertices P.pieces hp
  · intro i hi
    exact P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)
  · intro i j hij hj x hx hy
    by_cases he : j=i+1
    · subst j
      exact ⟨rfl,P.minimum_adjacent_intersection hmin i (by omega) hx hy⟩
    · exact False.elim ((Set.disjoint_left.mp (P.minimum_nonadjacent_disjoint hmin i j (by omega) hj)) hx hy)

end PolygonalChain

theorem exists_simple_polygonalChain_of_path {a b : Plane} (hab : a ≠ b) (γ : Path a b)
    (O : Set Plane) (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) :
    ∃ P : PolygonalChain O a b, Function.Injective P.path ∧ Set.range P.path ⊆ O ∧
      (∀ i, i+2 ≤ P.pieces →
        det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0) := by
  obtain ⟨P,hP,hmin⟩ := exists_minimum_polygonalChain_of_path γ O hO hγ
  exact ⟨P,P.minimum_path_injective hab hmin,hP,P.minimum_bend_det_ne_zero hmin⟩

end Zarankiewicz

end

end OAI
