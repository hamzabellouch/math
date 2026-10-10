import Mathlib
import OAI.Probability.SphericalField.Fields.CoupledDual
import OAI.Probability.SphericalField.Quantiles.Entropy

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma quantileTrial_congr {q p : Time → Time} (he : q=ᵐ[timeLaw] p) :
    quantileTrial q=quantileTrial p := by
  apply Trial.ext_fun
  intro t
  change (timeLaw {u | q u ≤ t}).toReal=(timeLaw {u | p u ≤ t}).toReal
  congr 1
  apply measure_congr
  filter_upwards [he] with u hu
  rw [hu]

lemma quantileTail_congr {q p : Time → Time} (he : q=ᵐ[timeLaw] p) (t : ℝ) :
    quantileTail q t=quantileTail p t := integral_congr_ae (he.mono fun u hu => by dsimp only; rw [hu])

lemma quantileA_congr {q p : Time → Time} (he : q=ᵐ[timeLaw] p) (r : ℝ) :
    quantileA q r=quantileA p r := by
  unfold quantileA
  simp_rw [quantileTail_congr he]

lemma clippedQuantile_ae_eq (q : Time → Time) (hq : Monotone q) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    (clippedQuantile q hq B hB0).toQuantile hB1.le=ᵐ[timeLaw] q := by
  filter_upwards [hb] with u hu
  apply Subtype.ext
  exact min_eq_left hu

lemma stationaryQuantileField_ae_eq (q : Time → Time) (hq : Monotone q) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    (stationaryQuantileField q hq B hB0 hB1 : Time → ℝ)=ᵐ[timeLaw] fun u => quantileA q (q u)/2 := by
  have he := clippedQuantile_ae_eq q hq hB0 hB1 hb
  filter_upwards [hb] with u hu
  change quantileA ((clippedQuantile q hq B hB0).toQuantile hB1.le) (min (q u:ℝ) B)/2=quantileA q (q u)/2
  rw [quantileA_congr he,min_eq_left hu]

lemma stationaryQuantileField_cross (q : Time → Time) (hq : Monotone q) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    (∫ u, (clippedQuantile q hq B hB0).stationary hB1 u*(clippedQuantile q hq B hB0) u ∂timeLaw)=
      ∫ u, stationaryQuantileField q hq B hB0 hB1 u*(q u:ℝ) ∂timeLaw := by
  apply integral_congr_ae
  filter_upwards [hb] with u hu
  change _*min (q u:ℝ) B=_*(q u:ℝ)
  rw [min_eq_left hu]
  rfl

lemma entropy_quantileTrial_finite_of_ae_bounded (q : Time → Time) (hq : Monotone q) {B : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    entropy (quantileTrial q) < ∞ := by
  rw [entropy_quantileTrial q hq.measurable B hB0 hB1 hb]
  exact ENNReal.ofReal_lt_top

end SphericalPerceptron
end
end

end OAI
