import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.DoubleAverage

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
lemma chord_average_integrable (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β))) :
    Integrable (fun y => ∫ x, (U y^β*dist y x*U x^β)^2
      ∂probability μ (fun x => U x^(2+4*β)))
      (probability μ (fun x => U x^(2+4*β))) := by
  let η := μ.withDensity (fun x => ENNReal.ofReal (U x^(2+6*β)))
  let : IsFiniteMeasure η := density_finite μ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _)
  have he (y : X) : squaredPotential η y = ∫ x, dist y x^2*U x^(2+6*β) ∂μ := by
    rw [squaredPotential,integral_density_nonnegative μ hi.aestronglyMeasurable
      (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _)]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hc := continuous_squaredPotential η
  have hf : AEStronglyMeasurable (fun y => U y^(2*β)*squaredPotential η y /
      total μ (fun x => U x^(2+4*β))) μ :=
    (((hU.pow_const _).mul hc.measurable).div_const _).aestronglyMeasurable
  simp_rw [chord_moment_identity μ hU.aestronglyMeasurable hU0 hb hW,←he]
  apply integrable_probability μ _ (hU.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW hf
  have hh : Integrable (fun y => U y^(2+6*β)*squaredPotential η y) μ := by
    simpa only [integrableOn_univ] using hi.integrableOn.mul_continuousOn hc.continuousOn isCompact_univ
  apply (hh.div_const _).congr
  filter_upwards [] with y
  rw [show (2+6*β:ℝ) = (2+4*β)+2*β by ring,
    Real.rpow_add' (hU0 y) (by linarith : 2+4*β+2*β ≠ 0)]
  ring

lemma average_lt_two (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hi0 : Integrable (fun x => U x^(2+4*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β)))
    (hpoint : ∀ᵐ y ∂probability μ (fun x => U x^(2+4*β)),
      (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β))) < 2) :
    (∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β))) < 2 := by
  let : IsProbabilityMeasure (probability μ (fun x => U x^(2+4*β))) :=
    isProbability μ _ hi0 (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW
  let ν := probability μ (fun x => U x^(2+4*β))
  let M (y : X) := ∫ x, (U y^β*dist y x*U x^β)^2 ∂ν
  have hiM : Integrable M ν := chord_average_integrable μ hU hU0 hb hi hW
  have hd : Integrable (fun y => 2-M y) ν := (integrable_const (2:ℝ)).sub hiM
  have hs : Function.support (fun y => 2-M y) =ᵐ[ν] (univ : Set X) := by
    filter_upwards [hpoint] with y hy
    change (2-M y ≠ 0) = True
    exact propext (iff_true_intro (sub_pos.mpr hy).ne')
  have hpos : 0 < ∫ y, (2-M y) ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpoint.mono fun y hy => (sub_pos.mpr hy).le) hd).mpr
    rw [measure_congr hs]
    simp
  rw [integral_sub (integrable_const (2:ℝ)) hiM,integral_const,
    measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hpos
  exact sub_pos.mp hpos
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
include q in
theorem density_contradiction (hX : IsCAT0 X) (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β)
    (hnb : (n:ℝ)*β = 1+2*β)
    (hi : Integrable (fun x => U x^(2+6*β)) (MassMeasure.currentMassMeasure hT))
    (hi0 : Integrable (fun x => U x^(2+4*β)) (MassMeasure.currentMassMeasure hT))
    (hW : 0 < ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))
    (hWs : ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)) < sphereArea n)
    (hall : ∀ y, (ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))^2 ≤
      (∫ x, U x^(2+6*β) ∂MassMeasure.currentMassMeasure hT)*
        (∫ x, dist y x^2*U x^(2+6*β) ∂MassMeasure.currentMassMeasure hT))
    (hd : ∀ (y : X) (a : ℝ), 0 ≤ a →
      ChordTransform.transform (ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2+4*β))) n (fun x => (U y^β*dist y x*U x^β)^2) a ≤
      (1+2*(∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))*a)^(-(n:ℝ)/2)) :
    False := by
  have he : 2*(n:ℝ)*β = 2+4*β := by linarith
  have ht := q.ae_current_tangent_density hn U hU hU0 hb
  have hi' : Integrable (fun x => U x^(2*(n:ℝ)*β)) (MassMeasure.currentMassMeasure hT) := by
    simpa only [he] using hi0
  have hW' : 0 < ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2*(n:ℝ)*β)) := by
    simpa only [he] using hW
  have hWs' : ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2*(n:ℝ)*β)) < sphereArea n := by
    simpa only [he] using hWs
  have hm : ∀ᵐ y ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2+4*β)),
      (∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β))) < 2 := by
    conv at ht => rw [he]
    filter_upwards [ht] with y hy
    have h := TangentDensity.moment_lt_two (MassMeasure.currentMassMeasure hT) U hU hU0 n y
      hi' hW' hWs' hy (by simpa only [he] using hd y)
    simpa only [he] using h
  have hlo := ChordMeasure.opposite_average (MassMeasure.currentMassMeasure hT) hX
    hU.aestronglyMeasurable hU0 hb hi hW hall
  have hup := ChordMeasure.average_lt_two (MassMeasure.currentMassMeasure hT) hU hU0 hb hi hi0 hW hm
  exact (not_lt_of_ge hlo) hup
end CAT0Fillings.ChartGeometry
end

end OAI
