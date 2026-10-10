import OAI.Combinatorics.Crossing.PolygonalChains

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_range_subset (v : ℕ → Plane) (O : Set Plane) (h0 : v 0 ∈ O) :
    (n : ℕ) → (∀ i, i < n → segment ℝ (v i) (v (i+1)) ⊆ O) →
      Set.range (polygonalArcPath v n) ⊆ O
  | 0, _ => by rintro x ⟨t,rfl⟩; exact h0
  | 1, h => by
    rw [polygonalArcPath,Path.range_segment]
    exact h 0 (by omega)
  | n+2, h => by
    rw [polygonalArcPath,Path.trans_range,Set.union_subset_iff]
    refine ⟨polygonalArcPath_range_subset v O h0 (n+1) (fun i hi => h i (by omega)),?_⟩
    rw [Path.range_segment]
    exact h (n+1) (by omega)

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem path_range_subset (P : PolygonalChain O a b) : Set.range P.path ⊆ O := by
  change Set.range (polygonalArcPath P.vertices P.pieces) ⊆ O
  exact polygonalArcPath_range_subset P.vertices O (by rw [P.first]; exact P.start_mem) P.pieces P.inside

end PolygonalChain

theorem exists_minimum_polygonalChain {O : Set Plane} {a b : Plane}
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces := by
  classical
  obtain ⟨P⟩ := h
  have hex : ∃ n : ℕ, ∃ Q : PolygonalChain O a b, Q.pieces=n := ⟨P.pieces,P,rfl⟩
  obtain ⟨Q,hQ⟩ := Nat.find_spec hex
  refine ⟨Q,?_⟩
  intro R
  rw [hQ]
  exact Nat.find_min' hex ⟨R,rfl⟩

theorem exists_minimum_polygonalChain_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) :
    ∃ P : PolygonalChain O a b, Set.range P.path ⊆ O ∧
      ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces := by
  obtain ⟨P,hP⟩ := exists_minimum_polygonalChain (nonempty_polygonalChain_of_path γ O hO hγ)
  exact ⟨P,P.path_range_subset,hP⟩

end Zarankiewicz

end

end OAI
