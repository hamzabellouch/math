import OAI.Probability.FreeIsing.Ising.OrientedGaussianTail
import OAI.Probability.FreeIsing.Ising.StemRerootAverage

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measure_extensionAverage_gt_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hb t inward stem (k + 1 + L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  exact (measure_extensionAverage_gt_le_restricted_average_ge hμ hb t inward stem hstem k L
    (orientationCutCost beta inward * Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ))).trans
      (measure_restrictedAverage_ge_le_double_exp hμ hb hd hcritical ht inward
        (stemForbidden stem) (card_stemForbidden_le_one stem) k L hη0 hℓ hη hηlog
        hlevel htail hlength)

theorem orientationCutCost_le_exp (hb : 0 ≤ beta) (inward : Bool) :
    orientationCutCost beta inward ≤ Real.exp (4 * beta / (1 - Real.tanh beta)) := by
  cases inward
  · change 1 ≤ Real.exp _
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (4 * beta / (1 - Real.tanh beta)) :=
        Real.exp_le_exp.mpr (div_nonneg (mul_nonneg (by norm_num) hb)
          (sub_nonneg.mpr (Real.tanh_lt_one beta).le))
  · exact le_rfl

theorem measure_extensionAverage_gt_le_double_exp_common
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | Real.exp (4 * beta / (1 - Real.tanh beta)) *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hb t inward stem (k + 1 + L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  refine le_trans (measure_mono ?_) (measure_extensionAverage_gt_le_double_exp
    hμ hb hd hcritical ht inward stem hstem k L hη0 hℓ hη hηlog hlevel htail hlength)
  intro x hx
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (orientationCutCost_le_exp hb inward)
    (Real.exp_pos _).le) hx

end Problem367.IsingOrientedPath

end

end OAI
