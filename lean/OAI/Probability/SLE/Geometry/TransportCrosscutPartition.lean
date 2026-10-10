import OAI.Probability.SLE.Geometry.SchoenfliesInsideTransport

namespace OAI

/-! Transport the proved polygonal crosscut theorem after an ambient
straightening of just the interior arc. -/
noncomputable section
open Set

namespace SLEExactGauge

theorem plane_homeomorph_arc (H : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) :
    Schoenflies.IsArcBetween (H '' A) (H p) (H q) := by
  obtain ⟨f,hfc,hfi,hfA,hf0,hf1⟩ := hA
  refine ⟨H ∘ f,H.continuous.comp_continuousOn hfc,?_,?_,?_,?_⟩
  · exact H.injective.injOn.comp hfi (mapsTo_univ _ _)
  · rw [image_comp,hfA]
  · exact congrArg H hf0
  · exact congrArg H hf1

theorem plane_crosscut_partition_of_straightening
    {C P A B : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C)
    (hP : Schoenflies.IsArcBetween P p q)
    (hcut : Schoenflies.IsCutPair C p q A B)
    (hp : p ∈ C) (hq : q ∈ C)
    (hin : P \ {p,q} ⊆ Schoenflies.inside C)
    (H : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (hpoly : Schoenflies.IsPolygonal (H '' P)) :
    Schoenflies.inside C \ P =
      Schoenflies.inside (A ∪ P) ∪ Schoenflies.inside (B ∪ P) ∧
    Disjoint (Schoenflies.inside (A ∪ P)) (Schoenflies.inside (B ∪ P)) := by
  have hc : Schoenflies.IsCrosscut (H '' C) (H '' P) (H p) (H q) := by
    refine ⟨plane_homeomorph_jordan H hC,plane_homeomorph_arc H hP,hpoly,
      mem_image_of_mem H hp,mem_image_of_mem H hq,?_⟩
    rw [← image_pair,← image_sdiff H.injective]
    exact (image_mono hin).trans (plane_homeomorph_inside H C).subset
  have hcuts : Schoenflies.IsCutPair (H '' C) (H p) (H q) (H '' A) (H '' B) := by
    refine ⟨plane_homeomorph_arc H hcut.fst,plane_homeomorph_arc H hcut.snd,?_,?_⟩
    · rw [← image_union,hcut.union_eq]
    · rw [← image_inter H.injective,hcut.inter_eq,image_pair]
  obtain ⟨he,hd,-⟩ := Schoenflies.crosscut_theorem hc hcuts
  refine ⟨?_,?_⟩
  · apply H.injective.image_injective
    simpa only [image_sdiff H.injective,plane_homeomorph_inside,image_union] using he
  · rw [Set.disjoint_left] at hd ⊢
    intro z hz hz'
    apply hd (a := H z)
    · simpa only [plane_homeomorph_inside,image_union] using mem_image_of_mem H hz
    · simpa only [plane_homeomorph_inside,image_union] using mem_image_of_mem H hz'

end SLEExactGauge

end

end OAI
