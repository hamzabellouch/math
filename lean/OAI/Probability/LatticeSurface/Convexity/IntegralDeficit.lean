import Mathlib

namespace OAI

namespace Density

open MeasureTheory Set

lemma integrable_nonneg_usc {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasureOnCompacts (volume:Measure E)]
    {p : E → ℝ} {R : ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,R<‖x‖ → p x=0) : Integrable p := by
  let K := Metric.closedBall (0:E) R
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨C,hC⟩ := (hp.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hi : IntegrableOn p K := (integrableOn_const hK.measure_ne_top (C:=C)).mono'
    hp.measurable.aestronglyMeasurable.restrict ?_
  · have he : K.indicator p=p := by
      funext x
      by_cases hx : x∈K
      · exact indicator_of_mem hx p
      · rw [indicator_of_notMem hx]
        exact (hpK x (by simpa [K,Metric.mem_closedBall,dist_zero_right,not_le] using hx)).symm
    rw [← he]
    exact hi.integrable_indicator hK.measurableSet
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (hp0 x)]
    exact hC (Set.mem_image_of_mem _ hx)

lemma integral_deficit {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p o : E → ℝ} {B : Set E} {k : ℝ}
    (hp : Integrable p μ) (ho : Integrable o μ) (hB : MeasurableSet B)
    (hk : k≤1) (_hp0 : ∀ x,0≤p x) (hglob : ∀ x,o x≤p x)
    (hgood : ∀ x∈B,o x≤k*p x) (hmass : (∫ x,p x ∂μ)/2≤∫ x in B,p x ∂μ) :
    (∫ x,o x ∂μ)≤(1-(1-k)/2)*(∫ x,p x ∂μ) := by
  have hbi := hp.indicator hB
  have hi := hp.sub (hbi.const_mul (1-k))
  have hh : (∫ x,o x ∂μ)≤∫ x,p x-(1-k)*B.indicator p x ∂μ := by
    apply integral_mono ho hi
    intro x
    change o x≤p x-(1-k)*B.indicator p x
    by_cases hx : x∈B
    · rw [Set.indicator_of_mem hx]
      linarith [hgood x hx]
    · rw [Set.indicator_of_notMem hx,mul_zero,sub_zero]
      exact hglob x
  rw [integral_sub hp (hbi.const_mul (1-k)),integral_const_mul,integral_indicator hB] at hh
  nlinarith [mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hk)]

end Density

end OAI
