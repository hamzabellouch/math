import OAI.Probability.SLE.Geometry.RandomSpatialTestingAE
import OAI.Probability.SLE.Mass.RadonTestFamily

namespace OAI

/-! A conditional measure kernel inherits the support of its past-measurable
comparison kernel. Localization only uses finite compact masses. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace SLEExactGauge

lemma restricted_random_set_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure X) (hμ : Measurable μ) (K : Set X) (hK : MeasurableSet K)
    (hfin : ∀ ω, μ ω K < ∞) (A : Set (Ω × X)) (hA : MeasurableSet A) :
    Measurable (fun ω => (μ ω).restrict K (Prod.mk ω ⁻¹' A)) := by
  have hm : Measurable (fun ω => (μ ω).restrict K) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.restrict_apply hS]
    exact (Measure.measurable_coe (hS.inter hK)).comp hμ
  let κ : Kernel Ω X := ⟨_,hm⟩
  exact Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hA
    (fun ω => ⟨by
      change (μ ω).restrict K univ < ∞
      simpa only [Measure.restrict_apply_univ] using hfin ω⟩)

lemma setLIntegral_random_indicator
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (A : Set (Ω × X)) (hA : MeasurableSet A) (ω : Ω) :
    (∫⁻ x in K, A.indicator (fun _ => (1 : ℝ≥0∞)) (ω,x) ∂μ) =
      μ.restrict K (Prod.mk ω ⁻¹' A) := by
  have he : (fun x => A.indicator (fun _ => (1 : ℝ≥0∞)) (ω,x)) =
      (Prod.mk ω ⁻¹' A).indicator (fun _ => 1) := by
    funext x
    by_cases hx : (ω,x) ∈ A <;> simp [hx]
  rw [he,lintegral_indicator (hA.preimage measurable_prodMk_left)]
  simp only [lintegral_one,Measure.restrict_apply_univ]

/-- If the conditional mean measures agree on every past event, then the
first measure gives no mass to any jointly past-measurable random set
which the second measure avoids. -/
theorem ae_avoids_random_set_of_conditional_kernel
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure X)
    (hμ : @Measurable Ω (Measure X) mΩ inferInstance μ)
    (hν : @Measurable Ω (Measure X) mΩ inferInstance ν)
    (K : ℕ → Set X) (hKm : ∀ n, MeasurableSet (K n))
    (hcover : ∀ x, ∃ n, x ∈ K n)
    (hμK : ∀ n ω, μ ω (K n) < ∞)
    (hνK : ∀ n, ∀ᵐ ω ∂P, ν ω (K n) < ∞)
    (hmean : ∀ n, P.bind μ (K n) < ∞)
    (hevent : ∀ E : Set Ω, MeasurableSet[m] E →
      (P.restrict E).bind μ = (P.restrict E).bind ν)
    (A : Set (Ω × X)) (hA : @MeasurableSet (Ω × X) (m.prod inferInstance) A)
    (hzero : ∀ ω, ν ω (Prod.mk ω ⁻¹' A) = 0) :
    ∀ᵐ ω ∂P, μ ω (Prod.mk ω ⁻¹' A) = 0 := by
  let : MeasurableSpace Ω := mΩ
  have hprod : m.prod (inferInstance : MeasurableSpace X) ≤
      mΩ.prod (inferInstance : MeasurableSpace X) :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  have hA' : MeasurableSet A := hprod _ hA
  have hn (n : ℕ) : ∀ᵐ ω ∂P, (μ ω).restrict (K n) (Prod.mk ω ⁻¹' A) = 0 := by
    have htest := conditional_random_spatial_test_on_ae m hm P μ ν hμ hν
      (K n) (hKm n) (Eventually.of_forall (hμK n)) (hνK n) (hmean n) hevent
      (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
    have hleft : (∫⁻ ω, (μ ω).restrict (K n) (Prod.mk ω ⁻¹' A) ∂P) = 0 := by
      simp_rw [setLIntegral_random_indicator _ _ _ hA'] at htest
      rw [htest]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with ω
      have hle : (ν ω).restrict (K n) ≤ ν ω := Measure.restrict_le_self
      exact le_zero_iff.mp ((hle _).trans_eq (hzero ω))
    exact (lintegral_eq_zero_iff (restricted_random_set_measurable μ hμ _ (hKm n)
      (hμK n) A hA')).mp hleft
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  have hsub : Prod.mk ω ⁻¹' A ⊆ ⋃ n, (Prod.mk ω ⁻¹' A) ∩ K n := by
    intro x hx
    obtain ⟨n,hn⟩ := hcover x
    exact mem_iUnion.mpr ⟨n,hx,hn⟩
  apply le_zero_iff.mp
  apply (measure_mono hsub).trans_eq
  apply measure_iUnion_null
  intro n
  rw [← Measure.restrict_apply (hA'.preimage measurable_prodMk_left)]
  exact hω n

end SLEExactGauge

end

end OAI
