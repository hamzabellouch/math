import OAI.Probability.SLE.Geometry.RationalTestPath

namespace OAI

/-! A countably measurable event guaranteeing zero initial mass, monotone
growth, and continuous compact-test paths for the raw rational reconstruction. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def RawRadonGood (D : LocalTestFamily upperHalfPlane) (μ : ℚ → Measure upperHalfPlane) : Prop :=
  HasContinuousRationalTests D μ ∧
  (∀ p q : ℚ, 0 ≤ p → p ≤ q → ∀ j,
    (∫ z, (D.test j ⊔ 0) z ∂μ p) ≤ ∫ z, (D.test j ⊔ 0) z ∂μ q) ∧
  ∀ j, (∫ z, D.test j z ∂μ 0)=0

lemma measurableSet_rawRadonGood {Y : Type*} [MeasurableSpace Y]
    (D : LocalTestFamily upperHalfPlane) (μ : ℚ → Y → Measure upperHalfPlane)
    (hm : ∀ q, Measurable (μ q)) (hr : ∀ q y, (μ q y).Regular) :
    MeasurableSet {y | RawRadonGood D (fun q => μ q y)} := by
  have htest (q : ℚ) (f : C_c(upperHalfPlane,ℝ)) :=
    measurable_halfPlane_compact_test_integral (μ q) (hm q) (hr q) f
  have hc := measurableSet_hasContinuousRationalTests D μ (fun q j => htest q (D.test j))
  have ho : MeasurableSet {y | ∀ p q : ℚ, 0 ≤ p → p ≤ q → ∀ j,
      (∫ z, (D.test j ⊔ 0) z ∂μ p y) ≤ ∫ z, (D.test j ⊔ 0) z ∂μ q y} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun j => measurableSet_le (htest p _) (htest q _)
  have hz : MeasurableSet {y | ∀ j, (∫ z, D.test j z ∂μ 0 y)=0} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (htest 0 (D.test j)) measurable_const
  simpa only [RawRadonGood,Set.ofPred_and] using hc.inter (ho.inter hz)

theorem RawRadonGood.reconstructed_paths
    (D : LocalTestFamily upperHalfPlane) (μ : ℚ → Measure upperHalfPlane)
    (hr : ∀ q, (μ q).Regular) (hg : RawRadonGood D μ) :
    let N := fun t => rationalRadonExtension (fun q (_ : Unit) => μ q) t ()
    N 0=0 ∧ Monotone N ∧ ∀ f : C_c(upperHalfPlane,ℝ),
      Continuous (fun t => ∫ z, f z ∂N t) := by
  dsimp only
  let N := fun t => rationalRadonExtension (fun q (_ : Unit) => μ q) t ()
  obtain ⟨hq,hc⟩ := HasContinuousRationalTests.continuous_extension D μ hr hg.1
  have hzero : μ 0=0 := by
    let := hr 0
    apply D.measure_eq_of_test_integrals
    intro j
    simpa only [integral_zero_measure] using hg.2.2 j
  have hz : N 0=0 := by
    have h := hq 0 le_rfl
    simpa only [Rat.cast_zero,Real.toNNReal_zero,hzero] using h
  refine ⟨hz,?_,hc⟩
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  let := (rationalRadonExtension_regular (fun q (_ : Unit) => μ q) s ()).1
  let := (rationalRadonExtension_regular (fun q (_ : Unit) => μ q) t ()).1
  apply radon_measure_le_of_nonneg_tests
  intro f hf
  have hlim (r : ℝ≥0) : Tendsto (fun n => ∫ z, f z ∂μ (leftRationalSample n r)) atTop
      (𝓝 (∫ z, f z ∂N r)) := by
    have he (n : ℕ) := hq (leftRationalSample n r) (leftRationalSample_nonneg n r)
    have ht := (continuous_real_toNNReal.tendsto (r:ℝ)).comp (leftRationalSample_tendsto r)
    simpa only [Real.toNNReal_coe,Function.comp_def,he] using
      (hc f).continuousAt.tendsto.comp ht
  have hlt : ∀ᶠ n in atTop, leftRationalSample n s ≤ leftRationalSample n t := by
    have hs := (leftRationalSample_tendsto s).eventually
      (gt_mem_nhds (show (s:ℝ)<((s:ℝ)+t)/2 by exact (by have := NNReal.coe_lt_coe.mpr hst; linarith)))
    have ht := (leftRationalSample_tendsto t).eventually
      (lt_mem_nhds (show ((s:ℝ)+t)/2<(t:ℝ) by exact (by have := NNReal.coe_lt_coe.mpr hst; linarith)))
    filter_upwards [hs,ht] with n hn hm
    exact Rat.cast_le.mp (hn.trans hm).le
  apply le_of_tendsto_of_tendsto (hlim s) (hlim t)
  filter_upwards [hlt] with n hn
  have hle : μ (leftRationalSample n s) ≤ μ (leftRationalSample n t) := by
    let := hr (leftRationalSample n s)
    let := hr (leftRationalSample n t)
    exact D.measure_le_of_positive_tests _ _
      (hg.2.1 _ _ (leftRationalSample_nonneg n s) hn)
  let := hr (leftRationalSample n t)
  exact integral_mono_measure hle (ae_of_all _ hf) f.integrable

theorem rawRadonGood_of_continuous_path
    (D : LocalTestFamily upperHalfPlane) (N : ℝ≥0 → Measure upperHalfPlane)
    (hr : ∀ t, (N t).Regular) (hz : N 0=0) (hm : Monotone N)
    (hc : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t)) :
    RawRadonGood D (fun q : ℚ => N (q:ℝ).toNNReal) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    refine ⟨⟨fun t => ∫ z, D.test j z ∂N t.toNNReal,
      (hc (D.test j)).comp continuous_real_toNNReal⟩,?_⟩
    rfl
  · intro p q _hp hpq j
    let := hr (q:ℝ).toNNReal
    exact integral_mono_measure (hm (Real.toNNReal_le_toNNReal (Rat.cast_le.mpr hpq)))
      (ae_of_all _ (fun _ => le_max_right _ _)) (D.test j ⊔ 0).integrable
  · intro j
    simp only [Rat.cast_zero,Real.toNNReal_zero,hz,integral_zero_measure]

end SLEExactGauge

end

end OAI
