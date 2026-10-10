import OAI.Combinatorics.Crossing.SimultaneousPolygonalReplacement

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonalChain.widen {S T : Set Plane} {a b : Plane} (P : PolygonalChain S a b)
    (hST : S ⊆ T) : PolygonalChain T a b where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first
  last := P.last
  start_mem := hST P.start_mem
  inside := fun i hi => (P.inside i hi).trans hST

theorem simple_path_interior_of_range_insert {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (O : Set Plane)
    (hrange : Set.range γ ⊆ insert a (insert b O))
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) : γ t ∈ O := by
  rcases hrange ⟨t,rfl⟩ with ha | hb | ho
  · have he := hinj (ha.trans γ.source.symm)
    exact False.elim (ht.1.ne he.symm)
  · have he := hinj (hb.trans γ.target.symm)
    exact False.elim (ht.2.ne he)
  · exact ho

theorem polygonal_replacement_with_spurs (O : Set Plane) (hO : IsOpen O)
    (a a' b' b : Plane) (hab : a ≠ b) (γ : Path a' b')
    (hγ : ∀ t, γ t ∈ O)
    (ha : segment ℝ a a' ⊆ insert a (insert b O))
    (hb : segment ℝ b' b ⊆ insert a (insert b O)) :
    ∃ P : PolygonalChain (insert a (insert b O)) a b,
      Function.Injective P.path ∧
      (∀ t : unitInterval, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ O) := by
  obtain ⟨Q⟩ := nonempty_polygonalChain_of_path γ O hO hγ
  let S := insert a (insert b O)
  let Q' : PolygonalChain S a' b' := Q.widen (fun _ hx => Or.inr (Or.inr hx))
  let L : PolygonalChain S a a' := PolygonalChain.single S a a' (Or.inl rfl) ha
  let R : PolygonalChain S b' b := PolygonalChain.single S b' b
    (Or.inr (Or.inr (by simpa using hγ 1))) hb
  obtain ⟨P,hP,hR⟩ := exists_simple_polygonalChain hab ⟨(L.join Q').join R⟩
  exact ⟨P,hP,fun t ht => simple_path_interior_of_range_insert P.path hP O hR t ht⟩

end Zarankiewicz

end

end OAI
