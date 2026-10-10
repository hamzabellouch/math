import OAI.Probability.SLE.Stochastic.PlanarWienerMoments

namespace OAI

/-! Riemann errors for bounded Lipschitz tests along planar Wiener paths. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarWiener_lipschitz_mean_error
    (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) (A : Set (Driver×Driver))
    (f : ℝ×ℝ → ℝ) (K L : ℝ≥0) (hb : ∀ z, |f z|≤K) (hf : LipschitzWith L f) :
    |∫ b in A, f (planarWiener s b)-f (planarWiener (s+δ) b) ∂W.prod W| ≤
      (L:ℝ)*2*Real.sqrt δ*standardGaussianAbsMoment 1 := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hi (t : ℝ≥0) : Integrable (fun b => f (planarWiener t b)) ((W.prod W).restrict A) :=
    Integrable.of_bound (hf.continuous.measurable.comp (measurable_planarWiener t)).aestronglyMeasurable K
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb _)
  have hni := planarWiener_increment_integrable W hW s δ
  calc
    _ ≤ ∫ b in A, |f (planarWiener s b)-f (planarWiener (s+δ) b)| ∂W.prod W := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := (W.prod W).restrict A) (fun b => f (planarWiener s b)-f (planarWiener (s+δ) b))
    _ ≤ ∫ b in A, (L:ℝ)*‖planarWiener (s+δ) b-planarWiener s b‖ ∂W.prod W := by
      apply integral_mono ((hi s).sub (hi (s+δ))).abs (hni.norm.restrict.const_mul _)
      intro b
      change |f (planarWiener s b)-f (planarWiener (s+δ) b)|≤_
      simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,abs_sub_comm] using
        hf.dist_le_mul (planarWiener (s+δ) b) (planarWiener s b)
    _ = (L:ℝ)*(∫ b in A, ‖planarWiener (s+δ) b-planarWiener s b‖ ∂W.prod W) := integral_const_mul _ _
    _ ≤ (L:ℝ)*(∫ b, ‖planarWiener (s+δ) b-planarWiener s b‖ ∂W.prod W) := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hni.norm (Eventually.of_forall fun b => norm_nonneg _)) L.coe_nonneg
    _ ≤ (L:ℝ)*(2*Real.sqrt δ*standardGaussianAbsMoment 1) :=
      mul_le_mul_of_nonneg_left (planarWiener_increment_norm_mean W hW s δ) L.coe_nonneg
    _ = _ := by ring

lemma planarWiener_integrated_drift_error
    (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) (A : Set (Driver×Driver))
    (f : ℝ×ℝ → ℝ) (K L : ℝ≥0) (hb : ∀ z, |f z|≤K) (hf : LipschitzWith L f) :
    |(δ:ℝ)*(∫ b in A, f (planarWiener s b) ∂W.prod W)-
      ∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), f (planarWiener u.toNNReal b)) ∂W.prod W| ≤
      (L:ℝ)*2*(δ:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 1 := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let C (u : ℝ) (b : Driver×Driver) := f (planarWiener s b)
  let D (u : ℝ) (b : Driver×Driver) := f (planarWiener u.toNNReal b)
  let G (u : ℝ) (b : Driver×Driver) := C u b-D u b
  have hC : Measurable (Function.uncurry C) :=
    (hf.continuous.measurable.comp (measurable_planarWiener s)).comp measurable_snd
  have ht : Measurable (fun q : ℝ×(Driver×Driver) => (q.1.toNNReal,q.2)) := by fun_prop
  have hD : Measurable (Function.uncurry D) :=
    hf.continuous.measurable.comp (planarWiener_joint_measurable.comp ht)
  have hG : Measurable (Function.uncurry G) := hC.sub hD
  have hCb (u b) : |C u b|≤K := hb _
  have hDb (u b) : |D u b|≤K := hb _
  have hGb (u b) : |G u b|≤2*(K:ℝ) := (abs_sub _ _).trans (by linarith [hCb u b,hDb u b])
  have hle : (s:ℝ)≤(s+δ:ℝ≥0) := by simp only [NNReal.coe_add]; linarith [δ.coe_nonneg]
  have hCI := bounded_interval_integral_integrable (P := (W.prod W).restrict A) _ _ hle C hC K hCb
  have hDI := bounded_interval_integral_integrable (P := (W.prod W).restrict A) _ _ hle D hD K hDb
  have he : (δ:ℝ)*(∫ b in A, C 0 b ∂W.prod W)-
      (∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), D u b) ∂W.prod W) =
      ∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), G u b) ∂W.prod W := by
    have hc : (∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), C u b) ∂W.prod W) =
        (δ:ℝ)*∫ b in A, C 0 b ∂W.prod W := by
      simp only [C,intervalIntegral.integral_const,NNReal.coe_add,add_sub_cancel_left,
        smul_eq_mul,integral_const_mul]
    rw [← hc,← integral_sub hCI hDI]
    apply integral_congr_ae
    exact Eventually.of_forall fun b => (intervalIntegral.integral_sub
      (bounded_time_section_intervalIntegrable _ _ hle C hC K hCb b)
      (bounded_time_section_intervalIntegrable _ _ hle D hD K hDb b)).symm
  change |(δ:ℝ)*(∫ b in A, C 0 b ∂W.prod W)-
    (∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), D u b) ∂W.prod W)|≤_
  rw [he]
  have hmean (u : ℝ) (hu : u ∈ Ioc (s:ℝ) (s+δ:ℝ≥0)) :
      |∫ b in A, G u b ∂W.prod W|≤(L:ℝ)*2*Real.sqrt δ*standardGaussianAbsMoment 1 := by
    have hus : s≤u.toNNReal := by
      exact_mod_cast (hu.1.le.trans (Real.le_coe_toNNReal u))
    have hud : u.toNNReal-s≤δ := by
      apply tsub_le_iff_right.mpr
      exact (Real.toNNReal_le_iff_le_coe).mpr (by simpa only [add_comm] using hu.2)
    have ht : s+(u.toNNReal-s)=u.toNNReal := add_tsub_cancel_of_le hus
    have hh := planarWiener_lipschitz_mean_error W hW s (u.toNNReal-s) A f K L hb hf
    rw [ht] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (standardGaussianAbsMoment_nonneg 1)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.sqrt_le_sqrt (by exact_mod_cast hud)
  have hh := bounded_interval_integral_expectation_bound (P := (W.prod W).restrict A)
    _ _ hle G hG (2*(K:ℝ)) ((L:ℝ)*2*Real.sqrt δ*standardGaussianAbsMoment 1) hGb hmean
  calc
    _ ≤ (L:ℝ)*2*Real.sqrt δ*standardGaussianAbsMoment 1*((s+δ:ℝ≥0)-s) := hh
    _ = _ := by simp only [NNReal.coe_add]; ring

end SLEExactGauge

end

end OAI
