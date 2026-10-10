import OAI.Analysis.LipschitzHilbert.Geometry.FarSlabGeometry
import OAI.Analysis.LipschitzHilbert.Estimates.BinaryDensityBound

namespace OAI

/-! Exact binary subdivision of the reference strips. Shared boundary
fibers have zero planar measure, so closed strip masses add exactly. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.Rectangle

theorem stripSlab_children (S : Rectangle) (c l : ℝ) :
    S.stripSlab c l = S.stripSlab (c-l/4) (l/2) ∪ S.stripSlab (c+l/4) (l/2) := by
  ext x
  simp only [stripSlab,mem_union,mem_preimage,mem_prod,mem_Icc]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hv⟩
    by_cases hm : (S.orthogonalCoordinates x).1 ≤ c
    · exact Or.inl ⟨⟨by linarith,by linarith⟩,hv⟩
    · exact Or.inr ⟨⟨by linarith,by linarith⟩,hv⟩
  · rintro (⟨⟨hlo,hhi⟩,hv⟩ | ⟨⟨hlo,hhi⟩,hv⟩) <;>
      exact ⟨⟨by linarith,by linarith⟩,hv⟩

theorem volume_coordinate_fiber (S : Rectangle) (c : ℝ) :
    volume {x | (S.orthogonalCoordinates x).1 = c} = 0 := by
  have he : {x | (S.orthogonalCoordinates x).1 = c} =
      S.orthogonalCoordinates ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by ext x; simp
  rw [he,S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod,measure_singleton,zero_mul]

theorem stripSlab_children_null_inter (S : Rectangle) (c l : ℝ) :
    volume (S.stripSlab (c-l/4) (l/2) ∩ S.stripSlab (c+l/4) (l/2)) = 0 := by
  apply measure_mono_null _ (S.volume_coordinate_fiber c)
  intro x hx
  have hxL := hx.1
  have hxR := hx.2
  change ((c-l/4)-(l/2)/2 ≤ (S.orthogonalCoordinates x).1 ∧
    (S.orthogonalCoordinates x).1 ≤ (c-l/4)+(l/2)/2) ∧ _ at hxL
  change ((c+l/4)-(l/2)/2 ≤ (S.orthogonalCoordinates x).1 ∧
    (S.orthogonalCoordinates x).1 ≤ (c+l/4)+(l/2)/2) ∧ _ at hxR
  change (S.orthogonalCoordinates x).1 = c
  linarith [hxL.1.2,hxR.1.1]

theorem intersection_stripSlab_children (S : Rectangle) {E : Set Plane}
    (hE : MeasurableSet E) (c l : ℝ) :
    volume (E ∩ S.stripSlab c l) =
      volume (E ∩ S.stripSlab (c-l/4) (l/2))+
        volume (E ∩ S.stripSlab (c+l/4) (l/2)) := by
  have hnull : volume ((E ∩ S.stripSlab (c-l/4) (l/2)) ∩
      (E ∩ S.stripSlab (c+l/4) (l/2))) = 0 := by
    apply measure_mono_null _ (S.stripSlab_children_null_inter c l)
    intro x hx
    exact ⟨hx.1.2,hx.2.2⟩
  have hm := measure_union_add_inter (μ := volume) (E ∩ S.stripSlab (c-l/4) (l/2))
    (hE.inter (S.isCompact_stripSlab (c+l/4) (l/2)).measurableSet)
  rw [hnull,add_zero] at hm
  rw [S.stripSlab_children c l,inter_union_distrib_left]
  exact hm

end LipschitzHilbert.Rectangle

namespace LipschitzHilbert

def stripMass {ι : Type*} (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)

theorem stripMass_children {ι : Type*} (R : ι → Rectangle) (s : Finset ι)
    (S : Rectangle) (c l : ℝ) :
    stripMass R s S c l = stripMass R s S (c-l/4) (l/2)+stripMass R s S (c+l/4) (l/2) := by
  unfold stripMass
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact S.intersection_stripSlab_children (R j).measurableSet_carrier c l

end LipschitzHilbert

end

end OAI
