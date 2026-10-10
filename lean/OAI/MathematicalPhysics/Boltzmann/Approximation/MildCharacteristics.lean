import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.AttenuationGap
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Jets.SpatialDilationAE

namespace OAI

section

/-! # The weak characteristic equation of the constructed mild states -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_along_flight {T t : ℝ} (ht : t ∈ Icc 0 T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,JetBarrier.flight t p) =
      TransportPrimitive.damped L (f₀ p) (fun r => g (r,JetBarrier.flight r p)) t := by
  rw [TransportPrimitive.damped_eq]
  unfold value
  rw [GaussianLocal.time_eq ht,JetFreeTransport.neg_flight]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [JetFreeTransport.flight_add,sub_add_cancel]

/-- The integral form of the transport equation, along almost every characteristic.
The source is only required to be measurable and bounded. -/
theorem weak_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p)))
    {ψ ψ' : ℝ → ℝ} (hψ : ContinuousOn ψ (Icc 0 T))
    (hψ' : ContinuousOn ψ' (Icc 0 T))
    (hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∫ t in 0..T, ψ' t*F (t,JetBarrier.flight t p) +
        ψ t*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p))) =
        ψ T*F (T,JetBarrier.flight T p)-ψ 0*f₀ p := by
  let A : ℝ × JetPrototype.Phase → ℝ := fun z => F (z.1,JetBarrier.flight z.1 z.2)
  let B : ℝ × JetPrototype.Phase → ℝ := fun z =>
    value T L JetBarrier.flight f₀ g (z.1,JetBarrier.flight z.1 z.2)
  have hflow : Measurable (fun z : ℝ × JetPrototype.Phase =>
      (z.1,JetBarrier.flight z.1 z.2)) :=
    measurable_fst.prodMk GaussianLocal.measurable_flight
  have hAm : Measurable A := hFm.comp hflow
  have hBm : Measurable B :=
    (measurable_value hT GaussianLocal.measurable_flight hf₀ hgm).comp hflow
  have hslice (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun p => A (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => B (t,p)) :=
    (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae (hmild t ht)
  have hall : A =ᵐ[(volume.restrict (Icc 0 T)).prod FlightMeasure.phaseVolume] B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hslice t ht
  have hp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)
  filter_upwards [hp,hslice T ⟨hT,le_rfl⟩] with p hpe hpend
  have hgi : IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)) volume 0 T := by
    apply (intervalIntegrable_const (c := S)).mono_fun'
    · exact (hgm.comp (measurable_id.prodMk
        (GaussianLocal.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hg (t,JetBarrier.flight t p))
  have H := TransportPrimitive.damped_integration_by_parts hT hgi hψ hψ' hdψ
    (L := L) (c := f₀ p)
  have he : (fun t => F (t,JetBarrier.flight t p)) =ᵐ[volume.restrict (Icc 0 T)]
      (fun t => TransportPrimitive.damped L (f₀ p) (fun r => g (r,JetBarrier.flight r p)) t) := by
    filter_upwards [hpe,ae_restrict_mem measurableSet_Icc] with t ht htm
    exact ht.trans (value_along_flight htm L f₀ g p)
  have hboundary : F (T,JetBarrier.flight T p) =
      TransportPrimitive.damped L (f₀ p) (fun r => g (r,JetBarrier.flight r p)) T :=
    hpend.trans (value_along_flight ⟨hT,le_rfl⟩ L f₀ g p)
  rw [hboundary]
  rw [← H]
  rw [intervalIntegral.integral_of_le hT,intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  have he' := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self he
  filter_upwards [he'] with t ht
  rw [ht]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Difference estimate for the positive mild iteration along a free path -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.MildStability

def value (f₀ : ℝ) (ν : ℝ → JetPrototype.Phase → ℝ) (g : ℝ → ℝ)
    (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  f₀ * JetPicardComparison.attenuation ν 0 t p +
    ∫ r in 0..t, JetPicardComparison.attenuation ν r t p * g r

private theorem product_difference {a b c d E M F : ℝ}
    (ha : |a| ≤ 1) (hcd : |c - d| ≤ E) (hd : |d| ≤ M) (hab : |a - b| ≤ F)
    (hF : 0 ≤ F) : |a * c - b * d| ≤ E + F * M := by
  calc
    _ = |a * (c - d) + (a - b) * d| := by congr 1; ring
    _ ≤ |a| * |c - d| + |a - b| * |d| := by simpa only [abs_mul] using abs_add_le (a * (c - d)) ((a - b) * d)
    _ ≤ 1 * E + F * M := add_le_add
      (mul_le_mul ha hcd (abs_nonneg _) (by norm_num))
      (mul_le_mul hab hd (abs_nonneg _) hF)
    _ = _ := by ring

theorem difference {ν μ : ℝ → JetPrototype.Phase → ℝ} {g h : ℝ → ℝ}
    {f₀ k₀ I A E M D t : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D)
    (p : JetPrototype.Phase)
    (hν : ∀ r ∈ Icc 0 t, 0 ≤ ν r (JetBarrier.flight r p))
    (hμ : ∀ r ∈ Icc 0 t, 0 ≤ μ r (JetBarrier.flight r p))
    (hνi : IntervalIntegrable (fun r => ν r (JetBarrier.flight r p)) volume 0 t)
    (hμi : IntervalIntegrable (fun r => μ r (JetBarrier.flight r p)) volume 0 t)
    (hνμ : ∀ r ∈ Icc 0 t, |ν r (JetBarrier.flight r p) - μ r (JetBarrier.flight r p)| ≤ D)
    (hfk : |f₀ - k₀| ≤ I) (hk : |k₀| ≤ A)
    (hgh : ∀ r ∈ Icc 0 t, |g r - h r| ≤ E) (hh : ∀ r ∈ Icc 0 t, |h r| ≤ M)
    (hgi : IntervalIntegrable (fun r => JetPicardComparison.attenuation ν r t p * g r) volume 0 t)
    (hhi : IntervalIntegrable (fun r => JetPicardComparison.attenuation μ r t p * h r) volume 0 t) :
    |value f₀ ν g t p - value k₀ μ h t p| ≤ I + D * t * A + (E + D * t * M) * t := by
  have hνsub (r : ℝ) (hr : r ∈ Icc 0 t) :
      IntervalIntegrable (fun τ => ν τ (JetBarrier.flight τ p)) volume r t := by
    apply hνi.mono_set
    rw [uIcc_of_le hr.2, uIcc_of_le ht]
    exact Icc_subset_Icc hr.1 le_rfl
  have hμsub (r : ℝ) (hr : r ∈ Icc 0 t) :
      IntervalIntegrable (fun τ => μ τ (JetBarrier.flight τ p)) volume r t := by
    apply hμi.mono_set
    rw [uIcc_of_le hr.2, uIcc_of_le ht]
    exact Icc_subset_Icc hr.1 le_rfl
  have had (r : ℝ) (hr : r ∈ Icc 0 t) :
      |JetPicardComparison.attenuation ν r t p - JetPicardComparison.attenuation μ r t p| ≤ D * t := by
    apply (AttenuationLipschitz.attenuation_difference_le hr.2 p
      (fun τ hτ => hν τ ⟨hr.1.trans hτ.1, hτ.2⟩)
      (fun τ hτ => hμ τ ⟨hr.1.trans hτ.1, hτ.2⟩)
      (hνsub r hr) (hμsub r hr) (fun τ hτ => hνμ τ ⟨hr.1.trans hτ.1, hτ.2⟩)).trans
    exact mul_le_mul_of_nonneg_left (sub_le_self t hr.1) hD
  have han (r : ℝ) (hr : r ∈ Icc 0 t) : |JetPicardComparison.attenuation ν r t p| ≤ 1 := by
    rw [abs_of_nonneg (JetPicardComparison.attenuation_nonneg _ _ _ _)]
    exact JetPicardComparison.attenuation_le_one hr.2 (fun τ hτ => hν τ ⟨hr.1.trans hτ.1, hτ.2⟩)
  have hinitial : |f₀ * JetPicardComparison.attenuation ν 0 t p -
      k₀ * JetPicardComparison.attenuation μ 0 t p| ≤ I + D * t * A := by
    simpa only [mul_comm f₀, mul_comm k₀] using product_difference (han 0 ⟨le_rfl, ht⟩)
      hfk hk (had 0 ⟨le_rfl, ht⟩) (mul_nonneg hD ht)
  have hpoint (r : ℝ) (hr : r ∈ Icc 0 t) :
      |JetPicardComparison.attenuation ν r t p * g r -
        JetPicardComparison.attenuation μ r t p * h r| ≤ E + D * t * M :=
    product_difference (han r hr) (hgh r hr) (hh r hr) (had r hr) (mul_nonneg hD ht)
  have hint : |(∫ r in 0..t, JetPicardComparison.attenuation ν r t p * g r) -
      ∫ r in 0..t, JetPicardComparison.attenuation μ r t p * h r| ≤ (E + D * t * M) * t := by
    rw [← intervalIntegral.integral_sub hgi hhi]
    apply (intervalIntegral.abs_integral_le_integral_abs ht).trans
    calc
      _ ≤ ∫ _r in 0..t, E + D * t * M :=
        intervalIntegral.integral_mono_on ht (hgi.sub hhi).abs intervalIntegrable_const hpoint
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring
  calc
    _ = |(f₀ * JetPicardComparison.attenuation ν 0 t p - k₀ * JetPicardComparison.attenuation μ 0 t p) +
        ((∫ r in 0..t, JetPicardComparison.attenuation ν r t p * g r) -
          ∫ r in 0..t, JetPicardComparison.attenuation μ r t p * h r)| := by unfold value; congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hinitial hint)

end BoltzmannNonuniqueness.MildStability

end

end

section

/-! # Exact dilation of the damped characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

def scalePhase (r : ℝ) (p : JetPrototype.Phase) : JetPrototype.Phase := (r • p.1,p.2)

theorem scalePhase_flight (r t : ℝ) (p : JetPrototype.Phase) :
    scalePhase r (JetBarrier.flight t p) = JetBarrier.flight (r*t) (scalePhase r p) := by
  apply Prod.ext
  · apply Prod.ext
    · change r • (p.1.1+t • VelocityWeight.transverse p.2) =
        r • p.1.1+(r*t) • VelocityWeight.transverse p.2
      rw [smul_add,mul_smul]
    · change r*(p.1.2+t*VelocityWeight.axial p.2) = r*p.1.2+(r*t)*VelocityWeight.axial p.2
      ring
  · rfl

theorem value_dilation {r T t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 T)
    (L : ℝ) (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value (r*T) L JetBarrier.flight f₀ g (r*t,scalePhase r p)/r =
      value T (r*L) JetBarrier.flight (fun p => f₀ (scalePhase r p)/r)
        (fun u => g (r*u.1,scalePhase r u.2)) (t,p) := by
  have hrt : r*t ∈ Icc 0 (r*T) :=
    ⟨mul_nonneg hr.le ht.1,mul_le_mul_of_nonneg_left ht.2 hr.le⟩
  unfold value
  rw [GaussianLocal.time_eq hrt,GaussianLocal.time_eq ht]
  have hi := intervalIntegral.integral_comp_mul_left
    (fun s => Real.exp (-L*(r*t-s))*g (s,JetBarrier.flight (s-r*t) (scalePhase r p))) hr.ne'
      (a := 0) (b := t)
  simp only [mul_zero,smul_eq_mul,← div_eq_inv_mul] at hi
  rw [add_div,← hi]
  have he : -L*(r*t) = -(r*L)*t := by ring
  have hp : JetBarrier.flight (-(r*t)) (scalePhase r p) = scalePhase r (JetBarrier.flight (-t) p) := by
    rw [scalePhase_flight]
    congr 1
    ring
  rw [he,hp]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro s _
    have he : -L*(r*t-r*s) = -(r*L)*(t-s) := by ring
    have hp : JetBarrier.flight (r*s-r*t) (scalePhase r p) = scalePhase r (JetBarrier.flight (s-t) p) := by
      rw [scalePhase_flight]
      congr 1
      ring
    dsimp only
    rw [he,hp]


theorem mild_dilation {r U A L : ℝ} (hr : 0 < r) (hA : r*A ≤ U)
    {f₀ : JetPrototype.Phase → ℝ} {F g : ℝ × JetPrototype.Phase → ℝ}
    (hmild : ∀ t ∈ Icc 0 U, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value U L JetBarrier.flight f₀ g (t,p))) :
    ∀ t ∈ Icc 0 A, (fun p => F (r*t,scalePhase r p)/r) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value A (r*L) JetBarrier.flight (fun p => f₀ (scalePhase r p)/r)
        (fun u => g (r*u.1,scalePhase r u.2)) (t,p)) := by
  intro t ht
  have hrt : r*t ∈ Icc 0 (r*A) :=
    ⟨mul_nonneg hr.le ht.1,mul_le_mul_of_nonneg_left ht.2 hr.le⟩
  have htU : r*t ∈ Icc 0 U := ⟨hrt.1,hrt.2.trans hA⟩
  have hae := (ColdDilationMeasure.spatial_dilation_quasiMeasurePreserving hr).ae (hmild (r*t) htU)
  filter_upwards [hae] with p hp
  calc
    F (r*t,scalePhase r p)/r = value U L JetBarrier.flight f₀ g (r*t,scalePhase r p)/r :=
      congrArg (fun z : ℝ => z/r) hp
    _ = value (r*A) L JetBarrier.flight f₀ g (r*t,scalePhase r p)/r :=
      congrArg (fun z : ℝ => z/r) (value_eq_at_time htU hrt.2 L f₀ (fun _ _ _ => rfl) _)
    _ = _ := value_dilation hr ht L f₀ g p

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Characteristic localization of bounded measurable mild solutions -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem characteristic_ae {T L : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (fun t => F (t,JetBarrier.flight t p)) =ᵐ[volume.restrict (Icc 0 T)]
        (fun t => TransportPrimitive.damped L (f₀ p)
          (fun r => g (r,JetBarrier.flight r p)) t) := by
  let A : ℝ × JetPrototype.Phase → ℝ := fun z => F (z.1,JetBarrier.flight z.1 z.2)
  let B : ℝ × JetPrototype.Phase → ℝ := fun z =>
    value T L JetBarrier.flight f₀ g (z.1,JetBarrier.flight z.1 z.2)
  have hflow : Measurable (fun z : ℝ × JetPrototype.Phase =>
      (z.1,JetBarrier.flight z.1 z.2)) :=
    measurable_fst.prodMk GaussianLocal.measurable_flight
  have hAm : Measurable A := hFm.comp hflow
  have hBm : Measurable B :=
    (measurable_value hT GaussianLocal.measurable_flight hf₀ hgm).comp hflow
  have hall : A =ᵐ[(volume.restrict (Icc 0 T)).prod FlightMeasure.phaseVolume] B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae (hmild t ht)
  have hp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)
  filter_upwards [hp] with p hpe
  filter_upwards [hpe,ae_restrict_mem measurableSet_Icc] with t ht htm
  exact ht.trans (value_along_flight htm L f₀ g p)

/-- The damping parameter of the iteration cancels, leaving the physical
source `g-L*F` plus the differentiated cutoff in a unit-damped formula. -/
theorem localized_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p)))
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      χ p T*F (T,JetBarrier.flight T p) = Real.exp (-T)*χ p 0*f₀ p +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) +
            (χ' p t+χ p t)*F (t,JetBarrier.flight t p)) := by
  have hp := characteristic_ae hT hf₀ hFm hgm hmild
  have ht := (FlightMeasure.flight_measurePreserving T).quasiMeasurePreserving.ae
    (hmild T ⟨hT,le_rfl⟩)
  filter_upwards [hp,ht] with p hpe hpend
  have hgi : IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)) volume 0 T := by
    apply (intervalIntegrable_const (c := S)).mono_fun'
    · exact (hgm.comp (measurable_id.prodMk
        (GaussianLocal.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hg (t,JetBarrier.flight t p))
  have H := TransportPrimitive.localized_damped hT hgi (hχ p) (hχ' p) (hdχ p)
    (L := L) (c := f₀ p)
  have hboundary := hpend.trans (value_along_flight ⟨hT,le_rfl⟩ L f₀ g p)
  rw [hboundary,H]
  congr 1
  rw [intervalIntegral.integral_of_le hT,intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  have he := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hpe
  filter_upwards [he] with t ht
  rw [ht]
  congr 1
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Undamped test identities along bounded mild characteristics -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem tested_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p)))
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∫ t in 0..T, χ' p t*F (t,JetBarrier.flight t p)+
        χ p t*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p))) =
      χ p T*F (T,JetBarrier.flight T p)-χ p 0*f₀ p := by
  have hp := characteristic_ae hT hf₀ hFm hgm hmild
  have ht := (FlightMeasure.flight_measurePreserving T).quasiMeasurePreserving.ae
    (hmild T ⟨hT,le_rfl⟩)
  filter_upwards [hp,ht] with p hpe hpend
  have hgi : IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)) volume 0 T := by
    apply (intervalIntegrable_const (c := S)).mono_fun'
    · exact (hgm.comp (measurable_id.prodMk
        (GaussianLocal.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hg (t,JetBarrier.flight t p))
  have H := TransportPrimitive.damped_integration_by_parts hT hgi (hχ p) (hχ' p) (hdχ p)
    (L := L) (c := f₀ p)
  have hb := hpend.trans (value_along_flight ⟨hT,le_rfl⟩ L f₀ g p)
  rw [hb]
  rw [← H]
  rw [intervalIntegral.integral_of_le hT,intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  have he := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hpe
  filter_upwards [he] with t ht
  rw [ht]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Survival of a positive datum under a bounded loss rate -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem survival_characteristic {T L B : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ B)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p)))
    (C : JetPrototype.Phase → ℝ)
    (hlow : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ t, t ∈ Ioc 0 T →
      -C p*F (t,JetBarrier.flight t p) ≤
        g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-C p*T)*f₀ p ≤ F (T,JetBarrier.flight T p) := by
  have ht := tested_characteristic hT hf₀ hFm hgm hg hmild
    (fun p t => Real.exp (C p*t)) (fun p t => C p*Real.exp (C p*t))
    (fun _ => (by fun_prop : Continuous _).continuousOn)
    (fun _ => (by fun_prop : Continuous _).continuousOn)
    (fun p t _ => by simpa [mul_comm] using ((hasDerivAt_id t).const_mul (C p)).exp)
  filter_upwards [ht,hlow] with p hp hpl
  have hi : 0 ≤ ∫ t in 0..T, C p*Real.exp (C p*t)*F (t,JetBarrier.flight t p)+
      Real.exp (C p*t)*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hT
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_of_ae hpl,ae_restrict_mem measurableSet_Ioc] with t ht htm
    have h := mul_le_mul_of_nonneg_left (ht htm) (Real.exp_pos (C p*t)).le
    change 0 ≤ C p*Real.exp (C p*t)*F (t,JetBarrier.flight t p)+
      Real.exp (C p*t)*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p))
    nlinarith only [h]
  rw [hp] at hi
  simp only [mul_zero,Real.exp_zero,one_mul] at hi
  have hm := mul_le_mul_of_nonneg_left (sub_nonneg.mp hi) (Real.exp_pos (-C p*T)).le
  have he : Real.exp (-C p*T)*Real.exp (C p*T) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  simpa only [← mul_assoc,he,one_mul] using hm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Removing the auxiliary damping from an actual mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem undamped_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F (T,JetBarrier.flight T p) = f₀ p+
        ∫ t in 0..T, g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p) := by
  have h := tested_characteristic hT hf₀ hFm hgm hg hmild
    (fun _ _ => 1) (fun _ _ => 0)
    (fun _ => continuous_const.continuousOn) (fun _ => continuous_const.continuousOn)
    (fun _ t _ => hasDerivAt_const t (1:ℝ))
  filter_upwards [h] with p hp
  simp only [zero_mul,one_mul,zero_add] at hp
  linarith

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # The undamped source is integrable along almost every finite characteristic -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem netSource_integrable_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p))
        volume 0 T := by
  filter_upwards [characteristic_ae hT hf₀ hFm hgm hmild] with p hp
  have hi : IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)) volume 0 T := by
    apply (intervalIntegrable_const (c := S)).mono_fun'
    · exact (hgm.comp (measurable_id.prodMk
        (GaussianLocal.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hg (t,JetBarrier.flight t p))
  have hd := TransportPrimitive.damped_continuousOn hT L (f₀ p) hi
  have hfi : IntervalIntegrable
      (TransportPrimitive.damped L (f₀ p) (fun t => g (t,JetBarrier.flight t p))) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hd
  have he : (fun t => F (t,JetBarrier.flight t p)) =ᵐ[volume.restrict (Ioc 0 T)]
      (TransportPrimitive.damped L (f₀ p) (fun t => g (t,JetBarrier.flight t p))) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hp
  have he' : (fun t => F (t,JetBarrier.flight t p)) =ᵐ[volume.restrict (uIoc 0 T)]
      (TransportPrimitive.damped L (f₀ p) (fun t => g (t,JetBarrier.flight t p))) := by
    simpa only [uIoc_of_le hT] using he
  exact hi.sub ((hfi.congr_ae he'.symm).const_mul L)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
