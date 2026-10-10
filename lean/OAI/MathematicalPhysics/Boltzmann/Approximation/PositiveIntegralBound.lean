import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics

namespace OAI

section

/-! # Scalar characteristic representatives for a.e. mild solutions -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem ae_path_bound_of_slices {T : ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    {A : ℝ → ℝ} (hFm : Measurable F) (hAm : Measurable A)
    (hbound : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F (t,p) ≤ A t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) T),
      F (t,JetBarrier.flight t p) ≤ A t := by
  have hm : Measurable (fun z : ℝ × JetPrototype.Phase =>
      F (z.1,JetBarrier.flight z.1 z.2)) :=
    hFm.comp (measurable_fst.prodMk GaussianLocal.measurable_flight)
  have hall : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod FlightMeasure.phaseVolume,
      F (z.1,JetBarrier.flight z.1 z.2) ≤ A z.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm (hAm.comp measurable_fst))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae (hbound t ht)
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)

theorem ae_characteristic_path {T t L : ℝ} (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hmild : ∀ s ∈ Icc 0 T, (fun p => F (s,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (s,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      ((fun r => F (r,JetBarrier.flight r p)) =ᵐ[volume.restrict (Icc (0:ℝ) t)]
        (fun r => TransportPrimitive.damped L (f₀ p)
          (fun s => g (s,JetBarrier.flight s p)) r)) ∧
      F (t,JetBarrier.flight t p) = TransportPrimitive.damped L (f₀ p)
        (fun s => g (s,JetBarrier.flight s p)) t := by
  let A : ℝ × JetPrototype.Phase → ℝ := fun z => F (z.1,JetBarrier.flight z.1 z.2)
  let B : ℝ × JetPrototype.Phase → ℝ := fun z =>
    value T L JetBarrier.flight f₀ g (z.1,JetBarrier.flight z.1 z.2)
  have hflow : Measurable (fun z : ℝ × JetPrototype.Phase =>
      (z.1,JetBarrier.flight z.1 z.2)) :=
    measurable_fst.prodMk GaussianLocal.measurable_flight
  have hAm : Measurable A := hFm.comp hflow
  have hBm : Measurable B := (measurable_value (ht.1.trans ht.2)
    GaussianLocal.measurable_flight hf₀ hgm).comp hflow
  have hslice (r : ℝ) (hr : r ∈ Icc 0 T) :
      (fun p => A (r,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => B (r,p)) :=
    (FlightMeasure.flight_measurePreserving r).quasiMeasurePreserving.ae (hmild r hr)
  have hall : A =ᵐ[(volume.restrict (Icc 0 t)).prod FlightMeasure.phaseVolume] B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hslice r ⟨hr.1,hr.2.trans ht.2⟩
  have hp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 t))).quasiMeasurePreserving.ae hall)
  filter_upwards [hp,hslice t ht] with p hpe hend
  constructor
  · filter_upwards [hpe,ae_restrict_mem measurableSet_Icc] with r hr hrmem
    exact hr.trans (value_along_flight ⟨hrmem.1,hrmem.2.trans ht.2⟩ L f₀ g p)
  · exact hend.trans (value_along_flight ht L f₀ g p)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Positive upper bounds for integrable signed characteristic sources -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ofReal_integral_le {f : X → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hm : Integrable (fun x => max (f x) 0) μ := hf.sup (integrable_zero X ℝ μ)
  calc
    _ ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono hf hm (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hm (ae_of_all _ (fun x => le_max_right _ _))
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_max,ENNReal.ofReal_zero]
      exact max_eq_left bot_le

theorem ofReal_add_intervalIntegral_le {a b c : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ENNReal.ofReal (c+∫ s in a..b, g s) ≤
      ENNReal.ofReal c+∫⁻ s in Ioc a b, ENNReal.ofReal (g s) := by
  apply ENNReal.ofReal_add_le.trans
  apply add_le_add le_rfl
  rw [intervalIntegral.integral_of_le hab]
  exact ofReal_integral_le hg.1

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
