import OAI.Analysis.LipschitzHilbert.Estimates.WeightedReferenceVariation
import OAI.Analysis.LipschitzHilbert.Estimates.ThresholdSynthesis
import OAI.Analysis.LipschitzHilbert.Estimates.WeightedIntegral

namespace OAI

/-! Measurable planar synthesis, threshold selection, and the weighted
variation integral in the reference chart (transverse, longitudinal). -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def scaleSynthesis (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (j : Fin N) (z : ℝ × ℝ) :
    EuclideanSpace ℂ κ := WithLp.toLp 2 (fun k => P.packets c z.1 j k z.2)

def variation (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ × ℝ) : ℝ :=
  cubicVariation (fun n => hilbertPartialBandSum (P.packets c z.1) n z.2) N

def thresholdSynthesis (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (z : ℝ × ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, if v z ≤ d j then P.scaleSynthesis c j z else 0

theorem thresholdSynthesis_le_variation (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (hd : Monotone d)
    (v : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ‖P.thresholdSynthesis c d v z‖ ≤ P.variation c z := by
  have heq : packetPartialSum (fun j => P.scaleSynthesis c j z) =
      (fun n => hilbertPartialBandSum (P.packets c z.1) n z.2) := by
    funext n
    exact (hilbertPartialBandSum_eq_packetPartialSum (P.packets c z.1) n z.2).symm
  simpa only [thresholdSynthesis, variation, heq] using
    threshold_sum_le_variation (fun j => P.scaleSynthesis c j z) d hd (v z)

theorem partialSynthesis_measurable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => hilbertPartialBandSum (P.packets c z.1) n z.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro k
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    unfold packets
    simp only [packetSynthesis_apply]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (hw j i k))
  · simpa only [ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0:ℂ)))

theorem variation_measurable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) :
    Measurable (P.variation c) :=
  (measurable_finiteCubicVariation _ (P.partialSynthesis_measurable c hw) N).pow_const _

theorem weightedVariationEnergy_eq (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (referenceWeight P.centerX P.centerZ P.radius P.width z ^ 2 * P.variation c z ^ 2)) =
      P.weightedVariationEnergy c := by
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal
    (referenceWeight P.centerX P.centerZ P.radius P.width z ^ 2 * P.variation c z ^ 2))
    (((referenceWeight_measurable _ _ _ _).pow_const 2).mul
      ((P.variation_measurable c hw).pow_const 2)).ennreal_ofReal.aemeasurable]
  unfold weightedVariationEnergy
  apply lintegral_congr
  intro y
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  simp only [referenceWeight, mul_pow, variation, cubicVariation_sq]
  rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_rpow_of_nonneg
      (finiteCubicVariation_nonneg _ _) (by norm_num : (0:ℝ) ≤ 2/3)]
  ac_rfl

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
