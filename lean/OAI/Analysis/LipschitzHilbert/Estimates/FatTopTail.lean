import OAI.Analysis.LipschitzHilbert.Geometry.FatEnclosure
import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiPacking

namespace OAI

/-! Weighted tails for actual fat tops. The same published input suffices:
the vertical enclosing rectangles are fully popular for a constant field. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem fat_top_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (D l r : ℝ),
      0 < D → (∀ i, 0 < (T i).clipLength D l r) →
      (∀ i, (T i).clipLength D l r ≤ 2*D*(T i).width) →
      (∀ i, |(T i).slope| ≤ 1) →
      ∀ (E : ι → Set (ℝ × ℝ)) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) → (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i, α*w i ≤ (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ,
      (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ≥0, 0 < t →
      (t:ℝ≥0∞)^2*α*(∑ i, if (t:ℝ)<a i then w i else 0) ≤
        (C:ℝ≥0∞)^2/(1/2:ℝ≥0∞)*(volume.prod volume) Q := by
  classical
  obtain ⟨C,hC,hbound⟩ := laceyLi_weighted_tail_fintype hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T D l r hD ha hfat hs E w α hEmeas hdisj hE hsize
    Q hQ hQfin hstrip a ha0 havg t ht
  let R : ι → Rectangle := fun i => (T i).fatEnclosure D l r (ha i) (hfat i)
  let E' : ι → Set Plane := fun i => planeCoordinates '' E i
  let Q' : Set Plane := planeCoordinates '' Q
  have hQ' : MeasurableSet Q' := planeCoordinates.measurableSet_image.mpr hQ
  have hQfin' : volume Q' ≠ ∞ := by simpa [Q',planeCoordinates_image_measure] using hQfin
  have hdisj' : Pairwise fun i j => Disjoint (E' i) (E' j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy : x = y := planeCoordinates.injective (hxz.trans hyz.symm)
    subst y
    exact disjoint_left.mp (hdisj hij) hx hy
  have havg' (i : ι) : ENNReal.ofReal (a i) ≤ (R i).average (Q'.indicator (fun _ => (1:ℝ))) := by
    have hinter : ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        volume (planeCoordinates '' (Q ∩ (T i).radialDilation D)) := by
      simpa only [planeCoordinates_image_measure] using havg i
    apply Rectangle.indicator_average_lower (R i) Q'
      (planeCoordinates '' (Q ∩ (T i).radialDilation D)) hQ' _
      (8*D^2*(T i).length*(T i).width) (a i)
      (by have := (T i).length_pos; have := (T i).width_pos; positivity) (ha0 i)
      ((T i).fatEnclosure_volume_le D l r hD (ha i) (hfat i) (hs i)) hinter
    rintro z ⟨x,⟨hxQ,hxD⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hxQ,(T i).mem_fatEnclosure D l r (ha i) (hfat i) x
      (hstrip x hxQ) hxD⟩
  have h := hbound (fun _ => verticalAxes 0) 0 (1/2) (LipschitzWith.const _)
    (fun _ => verticalAxes.norm_eq_one 0) (by norm_num) (by norm_num) ι R
    (fun i => (T i).fatEnclosure_admissible D l r (ha i) (hfat i)) E' w α
    (fun i => planeCoordinates.measurableSet_image.mpr (hEmeas i)) hdisj'
    (by
      intro i z hz
      obtain ⟨x,hx,rfl⟩ := hz
      exact (T i).mem_fatEnclosure D l r (ha i) (hfat i) x (hE i x hx).1 (hE i x hx).2)
    (by intro i; simpa [E',planeCoordinates_image_measure] using hsize i)
    (Q'.indicator (fun _ => (1:ℝ))) (memLp_indicator_const 2 hQ' 1 (Or.inr hQfin')) a havg' t ht
  have hh : ((1/2 : ℝ≥0) : ℝ≥0∞) = (1/2 : ℝ≥0∞) := by norm_num
  simpa only [squareIntegral_indicator Q' hQ', Q', planeCoordinates_image_measure, hh] using h

end LipschitzHilbert

end

end OAI
