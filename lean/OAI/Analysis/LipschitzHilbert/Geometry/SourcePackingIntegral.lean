import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxIntegralComparison
import OAI.Analysis.LipschitzHilbert.Trees.SourceReciprocalWeightEnergy

namespace OAI

/-! Bounded overlap controls sums of box integrals. The weighted envelope
pairing follows from the actual strong maximal kernel estimate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem sum_box_integrals_le {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (box : ι → Set X)
    (hbox : ∀ i∈S, MeasurableSet (box i)) (K : ℝ)
    (hcount : ∀ z, ((S.filter fun i => z∈box i).card:ℝ)≤K)
    (F : X → ℝ) (hF : Integrable F μ) (hF0 : ∀ z, 0≤F z) :
    (∑ i∈S, ∫ z in box i, F z ∂μ)≤K*∫ z, F z ∂μ := by
  classical
  have hi (i) (hi : i∈S) : Integrable ((box i).indicator F) μ := hF.indicator (hbox i hi)
  calc
    _ = ∫ z, ∑ i∈S, (box i).indicator F z ∂μ := by
      rw [integral_finsetSum _ hi]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_indicator (hbox i hi)).symm
    _ ≤ ∫ z, K*F z ∂μ := by
      apply integral_mono (integrable_finsetSum _ hi) (hF.const_mul K)
      intro z
      calc
        _ = (∑ i∈S, if z∈box i then (1:ℝ) else 0)*F z := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hz : z∈box i <;> simp [hz]
        _ = ((S.filter fun i => z∈box i).card:ℝ)*F z := by rw [Finset.sum_boole]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount z) (hF0 z)
    _ = _ := integral_const_mul _ _

theorem packed_weighted_envelope_pairing {ι : Type*}
    (S : Finset ι) (cx cy ell : ι → ℝ) (a b L W K : ℝ)
    (hL : 0<L) (hW : 0<W) (hell : ∀ i∈S, 0<ell i)
    (hlen : ∀ i∈S, ell i≤L)
    (hcount : ∀ z, ((S.filter fun i => z∈coordinateBox (cx i) (cy i) (ell i) W).card:ℝ)≤K)
    (H : ℝ×ℝ → ℝ) (hHm : Measurable H) (hH2 : MemLp H 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hH0 : ∀ z, 0≤H z) (hHb : ∀ z, ‖H z‖≤B) :
    (∑ i∈S, ∫ z, topReciprocalWeight a b L W z*tileEnvelope (cx i) (cy i) (ell i) W 2 z*H z
      ∂volume.prod volume)≤
        (82944*K)*∫ z, topReciprocalWeight a b L W z*DyadicLineGrid.threeStrongMaximal H z
          ∂volume.prod volume := by
  let D := topReciprocalWeight a b L W
  let M := DyadicLineGrid.threeStrongMaximal H
  have hD := (topReciprocalWeight_energy a b L W hL hW).1
  have hM := (DyadicLineGrid.threeStrongMaximal_energy hHm hH2).1
  have hF : Integrable (fun z => D z*M z) (volume.prod volume) := hD.integrable_mul hM
  have hF0 (z) : 0≤D z*M z := mul_nonneg (topReciprocalWeight_nonneg a b L W z)
    (DyadicLineGrid.threeStrongMaximal_nonneg H z)
  have hlocal (i : ι) (hi : i∈S) :
      (∫ z, D z*tileEnvelope (cx i) (cy i) (ell i) W 2 z*H z ∂volume.prod volume)≤
        82944*∫ z in coordinateBox (cx i) (cy i) (ell i) W, D z*M z ∂volume.prod volume := by
    have hp := weighted_tile_kernel_bound a b L W (cx i) (cy i) (ell i)
      (hell i hi) hW (hlen i hi) H hHm hH2 B hB hH0 hHb
    have hh := integral_comparison_on_box (cx i) (cy i) (ell i) W
      (∫ z, D z*tileEnvelope (cx i) (cy i) (ell i) W 2 z*H z ∂volume.prod volume)
      (36*9216) (hell i hi) hW (fun z => D z*M z) hF.integrableOn
      (hp.mono fun z hz hzc => by simpa only [mul_assoc] using hz hzc)
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ ∑ i∈S, 82944*∫ z in coordinateBox (cx i) (cy i) (ell i) W, D z*M z
        ∂volume.prod volume := Finset.sum_le_sum hlocal
    _ = 82944*∑ i∈S, ∫ z in coordinateBox (cx i) (cy i) (ell i) W, D z*M z
        ∂volume.prod volume := (Finset.mul_sum ..).symm
    _ ≤ 82944*(K*∫ z, D z*M z ∂volume.prod volume) := mul_le_mul_of_nonneg_left
      (sum_box_integrals_le (volume.prod volume) S _
        (fun i _ => coordinateBox_measurable _ _ _ _) K hcount _ hF hF0) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
