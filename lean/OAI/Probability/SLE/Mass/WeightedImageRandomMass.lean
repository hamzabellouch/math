import OAI.Probability.SLE.Mass.RestartRandomMassTesting

namespace OAI

/-! Measurable weighted images of locally finite random half-plane measures.
The weight and image map can be chosen from the stopped past. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped ENNReal

namespace SLEExactGauge

def weightedImageMass {X : Type*} [MeasurableSpace X]
    (J : upperHalfPlane → X) (w : upperHalfPlane → ℝ≥0∞)
    (μ : Measure upperHalfPlane) : Measure X :=
  (μ.withDensity w).map J

lemma weightedImageMass_apply {X : Type*} [MeasurableSpace X]
    (J : upperHalfPlane → X) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (μ : Measure upperHalfPlane)
    (A : Set X) (hA : MeasurableSet A) :
    weightedImageMass J w μ A = ∫⁻ z, (J ⁻¹' A).indicator w z ∂μ := by
  rw [weightedImageMass,Measure.map_apply hJ hA,withDensity_apply _ (hJ hA),
    lintegral_indicator (hJ hA)]

theorem weightedImageMass_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω))
    (J : Ω × upperHalfPlane → X) (hJ : Measurable J)
    (w : Ω × upperHalfPlane → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun ω => weightedImageMass (fun z => J (ω,z))
      (fun z => w (ω,z)) (μ ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have he (ω : Ω) := weightedImageMass_apply (fun z => J (ω,z))
    (hJ.comp (measurable_const.prodMk measurable_id)) (fun z => w (ω,z)) (μ ω) A hA
  simp_rw [he]
  exact halfPlane_random_test_measurable μ hμ hfin
    ((J ⁻¹' A).indicator w) (hw.indicator (hJ hA))

lemma weightedImageMass_lintegral {X : Type*} [MeasurableSpace X]
    (J : upperHalfPlane → X) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w)
    (μ : Measure upperHalfPlane) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂weightedImageMass J w μ) = ∫⁻ z, w z*f (J z) ∂μ := by
  rw [weightedImageMass,lintegral_map hf hJ]
  exact lintegral_withDensity_eq_lintegral_mul μ hw
    (show Measurable (fun z => f (J z)) from hf.comp hJ)

theorem weightedImageMass_measurable_of_subsigma
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable[mΩ] μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω))
    (J : Ω × upperHalfPlane → X) (hJ : Measurable[m.prod inferInstance] J)
    (w : Ω × upperHalfPlane → ℝ≥0∞) (hw : Measurable[m.prod inferInstance] w) :
    Measurable[mΩ] (fun ω => weightedImageMass (fun z => J (ω,z))
      (fun z => w (ω,z)) (μ ω)) := by
  let : MeasurableSpace Ω := mΩ
  have hle : m.prod (inferInstance : MeasurableSpace upperHalfPlane) ≤ mΩ.prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  exact weightedImageMass_measurable μ hμ hfin J (hJ.mono hle le_rfl) w (hw.mono hle le_rfl)

theorem restart_weighted_mass_test
    {Ω X Y : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (V : Ω → X) (hV : Measurable[mΩ] V)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX V (P.restrict A) = P A • ν)
    (M : X → Measure upperHalfPlane) (hM : Measurable M)
    (hMf : ∀ x, IsFiniteMeasureOnCompacts (M x))
    (J : Ω × upperHalfPlane → Y) (hJ : Measurable[m.prod inferInstance] J)
    (w : Ω × upperHalfPlane → ℝ≥0∞) (hw : Measurable[m.prod inferInstance] w)
    (f : Ω × Y → ℝ≥0∞) (hf : Measurable[m.prod mY] f) :
    (∫⁻ ω, ∫⁻ y, f (ω,y) ∂weightedImageMass (fun z => J (ω,z))
        (fun z => w (ω,z)) (M (V ω)) ∂P) =
      ∫⁻ ω, ∫⁻ z, w (ω,z)*f (ω,J (ω,z)) ∂ν.bind M ∂P := by
  let : MeasurableSpace Ω := mΩ
  have htest : Measurable[m.prod inferInstance]
      (fun p : Ω × upperHalfPlane => w p*f (p.1,J p)) :=
    hw.mul (hf.comp (measurable_fst.prodMk hJ))
  have he (ω : Ω) := weightedImageMass_lintegral (fun z => J (ω,z))
    (hJ.comp (measurable_const.prodMk measurable_id)) (fun z => w (ω,z))
    (hw.comp (measurable_const.prodMk measurable_id)) (M (V ω)) (fun y => f (ω,y))
    (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  exact restart_random_mass_test P ν m hm V hV hlaw M hM hMf _ htest

end SLEExactGauge

end

end OAI
