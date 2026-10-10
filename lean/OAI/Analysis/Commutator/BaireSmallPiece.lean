import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.BaireSmallPiece

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MetricSpace E]

theorem exists_open_piece (j : X → E) {C : Set X} (hC : IsCompact C)
    (hne : C.Nonempty) (hsep : IsSeparable (j '' C))
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y≤r})
    (ε : ℝ) (hε : 0<ε) :
    ∃ U : Set X,IsOpen U ∧ (C∩U).Nonempty ∧
      ∀ x∈C∩U,∀ y∈C∩U,dist (j x) (j y)<ε := by
  classical
  obtain ⟨D,hDc,hD⟩ := hsep
  have : Countable D := hDc.to_subtype
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have : Nonempty C := hne.to_subtype
  let A : D → Set C := fun d => {x | dist (j x) d≤ε/4}
  have hAc (d : D) : IsClosed (A d) := (hball d (ε/4)).preimage continuous_subtype_val
  have hAu : ⋃ d,A d=univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    have hx : j x∈closure D := hD ⟨x,x.property,rfl⟩
    obtain ⟨d,hd,hxd⟩ := Metric.mem_closure_iff.mp hx (ε/4) (by positivity)
    exact mem_iUnion.mpr ⟨⟨d,hd⟩,hxd.le⟩
  obtain ⟨d,hd⟩ := nonempty_interior_of_iUnion_of_closed hAc hAu
  obtain ⟨U,hU,hUi⟩ := isOpen_induced_iff.mp (show IsOpen (interior (A d)) from isOpen_interior)
  refine ⟨U,hU,?_,?_⟩
  · obtain ⟨x,hx⟩ := hd
    refine ⟨x,x.property,?_⟩
    have hx' : x∈Subtype.val ⁻¹' U := by rw [hUi]; exact hx
    exact hx'
  · intro x hx y hy
    have hxd : dist (j x) d≤ε/4 := by
      change (⟨x,hx.1⟩ : C)∈A d
      apply interior_subset (s:=A d)
      rw [←hUi]
      exact (show (⟨x,hx.1⟩ : C)∈Subtype.val ⁻¹' U from hx.2)
    have hyd : dist (j y) d≤ε/4 := by
      change (⟨y,hy.1⟩ : C)∈A d
      apply interior_subset (s:=A d)
      rw [←hUi]
      exact (show (⟨y,hy.1⟩ : C)∈Subtype.val ⁻¹' U from hy.2)
    calc
      dist (j x) (j y) ≤ dist (j x) d+dist (d : E) (j y) := dist_triangle _ _ _
      _ ≤ ε/4+ε/4 := add_le_add hxd (by simpa only [dist_comm] using hyd)
      _ < ε := by linarith

end Kadison.BaireSmallPiece

end

end
end

end OAI
