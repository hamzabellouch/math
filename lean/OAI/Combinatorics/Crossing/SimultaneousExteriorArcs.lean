import OAI.Combinatorics.Crossing.ExteriorArcReplacement

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_exterior_arc_replacements {E M : Type*}
    [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]
    (z : M → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : E → M) (a b : E → Plane) (hab : ∀ e, a e ≠ b e)
    (ha : ∀ e, squaredLength (a e-z (k e))=r^2)
    (hb : ∀ e, squaredLength (b e-z (l e))=r^2)
    (γ : ∀ e, Path (a e) (b e))
    (hdisjoint : ∀ e f, e ≠ f → Disjoint (Set.range (γ e)) (Set.range (γ f)))
    (hγ : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ e t ∈ outsideDisks z r) :
    ∃ U : E → Set Plane, ∃ P : ∀ e, PolygonalChain (U e) (a e) (b e),
      (∀ e, IsOpen (U e)) ∧ (∀ e, Function.Injective (P e).path) ∧
      (∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → (P e).path t ∈ outsideDisks z r) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (P e).path) (Set.range (P f).path)) := by
  obtain ⟨U,hU,hKU,_,hUU⟩ := finite_compact_corridors (fun e => Set.range (γ e))
    (fun _ => Set.univ) (fun e => isCompact_range (γ e).continuous) hdisjoint
    (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  have hex (e : E) : ∃ P : PolygonalChain (U e) (a e) (b e), Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) :=
    exterior_arc_polygonal_replacement z r hr hd (k e) (l e) (a e) (b e) (hab e)
      (ha e) (hb e) (γ e) (U e) (hU e) (fun t => hKU e ⟨t,rfl⟩) (hγ e)
  choose P hP hR using hex
  exact ⟨U,P,hU,hP,hR,fun e f hef =>
    (hUU e f hef).mono (P e).path_range_subset (P f).path_range_subset⟩

end Zarankiewicz

end

end OAI
