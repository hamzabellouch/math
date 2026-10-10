import OAI.Analysis.LipschitzHilbert.Estimates.TopDilationTail
import OAI.Analysis.LipschitzHilbert.Estimates.TopAreaAverage
import OAI.Analysis.LipschitzHilbert.Estimates.SquareTailLayer

namespace OAI

/-! Actual intersection averages, weighted by top area, satisfy the cubic
dilation testing estimate. No cardinality factor occurs. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem top_dilation_packing (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (l r D : ℝ), 1 ≤ D → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      0 < ∑ i, (T i).area →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) →
      (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation D)) ≤
        ENNReal.ofReal ((C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*D^3*
          Real.sqrt ((volume.prod volume).real Q)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := top_dilation_square_tail hLL
  refine ⟨64*(C:ℝ), by positivity, ?_⟩
  intro ι _ T l r D hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose hsize
    hS Q hQ hQfin hstrip
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hQzero : (volume.prod volume) Q = 0
  · have hi (i : ι) : (volume.prod volume) (Q ∩ (T i).radialDilation D) = 0 :=
      measure_mono_null inter_subset_left hQzero
    simp only [hi, Finset.sum_const_zero]
    exact zero_le
  have hQpos : 0 < (volume.prod volume).real Q := ENNReal.toReal_pos hQzero hQfin
  let B : ℝ := (4*(C:ℝ)*D/(α:ℝ))*Real.sqrt ((volume.prod volume).real Q)
  have hB : 0 < B := by dsimp [B]; exact mul_pos (by positivity) (Real.sqrt_pos.mpr hQpos)
  have hBsq : B^2 = (4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt hQpos.le]
  have htail := hbound ι T D l r hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE
    hclose hsize Q hQ hQfin hstrip (fun i => (T i).dilationAverage D Q)
    (fun i => (T i).dilationAverage_nonneg D Q)
    (fun i => ((T i).dilationAverage_normalized D hDpos Q hQfin).le)
  have hlayer := weighted_layer_from_square_tail (fun i => (T i).areaWeight)
    (fun i => (T i).dilationAverage D Q) (fun i => (T i).dilationAverage_nonneg D Q)
    B hB (by simpa using hS) (by
      intro t ht
      simpa only [SlopeBox.ennreal_areaWeight, SlopeBox.area, hBsq] using htail t ht)
  rw [SlopeBox.sum_dilation_intersection_eq T D hDpos Q hQfin]
  calc
    _ ≤ ENNReal.ofReal (8*D^2)*ENNReal.ofReal
        (2*B*Real.sqrt (∑ i, ((T i).areaWeight:ℝ))) := mul_le_mul' le_rfl hlayer
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      simp only [SlopeBox.coe_areaWeight]
      congr 1
      dsimp [B]
      ring

end LipschitzHilbert

end

end OAI
