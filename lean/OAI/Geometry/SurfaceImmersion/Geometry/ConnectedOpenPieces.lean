import OAI.Geometry.SurfaceImmersion.Geometry.SubarcTopology

namespace OAI

/-! Connected open pieces with frontier in a deleted vertex set either
coincide or are disjoint. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem connected_open_pieces_equal_or_disjoint
    {S T V : Set X} (hSo : IsOpen S) (hTo : IsOpen T)
    (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    (hSb : closure S \ S ⊆ V) (hTb : closure T \ T ⊆ V)
    (hSV : Disjoint S V) (hTV : Disjoint T V) : S = T ∨ Disjoint S T := by
  by_cases hd : Disjoint S T
  · exact Or.inr hd
  left
  have hi : (S ∩ T).Nonempty := not_disjoint_iff_nonempty_inter.mp hd
  have hTS : T ⊆ S := hTc.subset_of_closure_inter_subset hSo (by simpa only [inter_comm] using hi)
    (by
      intro x hx
      by_contra hn
      exact disjoint_left.mp hTV hx.2 (hSb ⟨hx.1,hn⟩))
  have hST : S ⊆ T := hSc.subset_of_closure_inter_subset hTo hi
    (by
      intro x hx
      by_contra hn
      exact disjoint_left.mp hSV hx.2 (hTb ⟨hx.1,hn⟩))
  exact Subset.antisymm hST hTS

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
