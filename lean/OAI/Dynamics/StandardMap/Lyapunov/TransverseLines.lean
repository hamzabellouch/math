import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.InverseLyapunov

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardLyapunov_iterate (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    standardLyapunov k hk ((standardMap k)^[n] z)=standardLyapunov k hk z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', standardLyapunov_invariant, ih]

lemma ae_stableVector_product_covariant (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((standardMap k)^[n] z))
        (standardDerivativeProduct k z n (stableVector k z))=0 := by
  induction n with
  | zero => exact Eventually.of_forall fun z _ => by simp only [standardDerivativeProduct_zero, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]; dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_stableVector_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_iterate] using hp)
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma standardDerivativeProduct_inverse (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k ((standardMap k)^[n] z) n
      (standardDerivativeProduct k z n v)=v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply,
      ← standardInverseDerivativeProduct_shift, Function.iterate_succ_apply',
      inverseMap_standardMap, standardInverseDerivative_standardDerivative, ih]

lemma standardDerivativeProduct_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    ‖standardDerivativeProduct k z n‖ ≤ (9*growthBase k)^n := by
  induction n with
  | zero => simp [standardDerivativeProduct]
  | succ n ih =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        rw [pow_succ']
        exact mul_le_mul (standardDerivative_norm_bound k hk _) ih
          (norm_nonneg _) (by have := growthBase_ge_four k hk; positivity))

lemma standardInverseDerivativeProduct_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    ‖standardInverseDerivativeProduct k z n‖ ≤ (9*growthBase k)^n := by
  induction n with
  | zero => simp [standardInverseDerivativeProduct]
  | succ n ih =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        rw [pow_succ']
        exact mul_le_mul (standardInverseDerivative_norm_bound k hk _) ih
          (norm_nonneg _) (by have := growthBase_ge_four k hk; positivity))

lemma area_unit_log_abs_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {v : ℂ} (hv : ‖v‖=1) : |Real.log ‖A v‖| ≤ Real.log ‖A‖ := by
  have hpA : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hpv : 0 < ‖A v‖ := by
    have hh := hA.norm_lower v
    rw [hv] at hh
    by_contra h
    have hz : ‖A v‖=0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, mul_zero] at hh
    norm_num at hh
  have hupper : ‖A v‖ ≤ ‖A‖ := by simpa only [hv, mul_one] using A.le_opNorm v
  have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 1)
    (show 1 ≤ ‖A‖*‖A v‖ by simpa only [hv] using hA.norm_lower v)
  rw [Real.log_one, Real.log_mul hpA.ne' hpv.ne'] at hlower
  exact abs_le.mpr ⟨by linarith, Real.log_le_log hpv hupper⟩

lemma area_unit_rate_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {v : ℂ} (hv : ‖v‖=1) {K : ℝ} (hK : 1≤K) (n : ℕ) (hbound : ‖A‖ ≤ K^n) :
    |Real.log ‖A v‖/(n : ℝ)| ≤ Real.log K := by
  have hKpos : 0<K := lt_of_lt_of_le zero_lt_one hK
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2) hbound
  rw [Real.log_pow] at hlog
  have hh := (area_unit_log_abs_bound A hA hv).trans hlog
  rw [abs_div, Nat.abs_cast]
  by_cases hn : n=0
  · simp only [hn, Nat.cast_zero, div_zero]; exact Real.log_nonneg hK
  · exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ)<n)).mpr (by nlinarith)

noncomputable def stableGrowthAverage (k : ℝ) (n : ℕ) (z : Torus) : ℝ :=
  Real.log ‖standardDerivativeProduct k z n (stableVector k z)‖/(n : ℝ)
noncomputable def stableBackwardAverage (k : ℝ) (n : ℕ) (z : Torus) : ℝ :=
  Real.log ‖standardInverseDerivativeProduct k z n (stableVector k z)‖/(n : ℝ)

lemma measurable_stableGrowthAverage (k : ℝ) (n : ℕ) : Measurable (stableGrowthAverage k n) :=
  ((((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((continuous_standardDerivativeProduct k n).measurable.prodMk (measurable_stableVector k))).norm).log).div_const _
lemma measurable_stableBackwardAverage (k : ℝ) (n : ℕ) : Measurable (stableBackwardAverage k n) :=
  ((((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((continuous_standardInverseDerivativeProduct k n).measurable.prodMk (measurable_stableVector k))).norm).log).div_const _

lemma stableGrowthAverage_bound (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    |stableGrowthAverage k n z| ≤ Real.log (9*growthBase k) :=
  area_unit_rate_bound _ (standardDerivativeProduct_area k z n) (norm_stableVector k z)
    (by have := growthBase_ge_four k hk; linarith) n (standardDerivativeProduct_norm_bound k hk z n)
lemma stableBackwardAverage_bound (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    |stableBackwardAverage k n z| ≤ Real.log (9*growthBase k) :=
  area_unit_rate_bound _ (standardInverseDerivativeProduct_area k z n) (norm_stableVector k z)
    (by have := growthBase_ge_four k hk; linarith) n (standardInverseDerivativeProduct_norm_bound k hk z n)

lemma ae_stable_averages_cancel (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      stableGrowthAverage k n z + stableBackwardAverage k n ((standardMap k)^[n] z)=0 := by
  filter_upwards [ae_stableVector_product_covariant k hk n] with z hz hp
  let v := standardDerivativeProduct k z n (stableVector k z)
  let s := stableVector k ((standardMap k)^[n] z)
  have he : v = dot s v • s := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
  have hnorm : ‖v‖ = |dot s v| := by
    conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, show ‖s‖=1 from norm_stableVector k _, mul_one]
  have hmul : ‖v‖ * ‖standardInverseDerivativeProduct k ((standardMap k)^[n] z) n s‖ = 1 := by
    calc
      _ = ‖standardInverseDerivativeProduct k ((standardMap k)^[n] z) n v‖ := by
        conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs, ← hnorm]
      _ = 1 := by rw [standardDerivativeProduct_inverse, norm_stableVector]
  have hpv := PlaneLyapunov.image_norm_pos _ (standardDerivativeProduct_area k z)
    (stableVector_ne_zero k z) n
  have hps := PlaneLyapunov.image_norm_pos _ (standardInverseDerivativeProduct_area k ((standardMap k)^[n] z))
    (stableVector_ne_zero k ((standardMap k)^[n] z)) n
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hpv.ne' hps.ne', Real.log_one] at hlog
  unfold stableGrowthAverage stableBackwardAverage
  rw [← add_div, hlog, zero_div]

lemma measurePreserving_coincidentLines (k : ℝ) (hk : 0≤k) :
    MeasurePreserving (standardMap k) (area.restrict (coincidentLines k hk))
      (area.restrict (coincidentLines k hk)) := by
  have hh := (measurePreserving_standardMap k).restrict_preimage (measurableSet_coincidentLines k hk)
  rw [Measure.restrict_congr_set (preimage_coincidentLines_ae k hk)] at hh
  exact hh

lemma ae_coincident_backward_growth (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area.restrict (coincidentLines k hk), Tendsto (fun n => stableBackwardAverage k n z)
      atTop (𝓝 (-standardLyapunov k hk z)) := by
  filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
    (ae_unstableVector_growth k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz hg
  have hw : wedge (unstableVector k z) (stableVector k z)=0 := by
    rw [wedge_swap, hz.2, neg_zero]
  exact (PlaneLyapunov.growth_on_line _ (standardInverseDerivativeProduct_area k z)
    (norm_unstableVector k z) (hg hz.1) (stableVector k z) (stableVector_ne_zero k z) hw).2

theorem measure_coincidentLines_zero (k : ℝ) (hk : 0≤k) : area (coincidentLines k hk)=0 := by
  let μ := area.restrict (coincidentLines k hk)
  let C := Real.log (9*growthBase k)
  have ha (n) : Integrable (stableGrowthAverage k n) μ :=
    Integrable.mono' (integrable_const C) (measurable_stableGrowthAverage k n).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableGrowthAverage_bound k hk n z)
  have hb (n) : Integrable (stableBackwardAverage k n) μ :=
    Integrable.mono' (integrable_const C) (measurable_stableBackwardAverage k n).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableBackwardAverage_bound k hk n z)
  have hla : Tendsto (fun n => ∫ z, stableGrowthAverage k n z ∂μ) atTop
      (𝓝 (∫ z, -standardLyapunov k hk z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Torus => C)
      (fun n => (measurable_stableGrowthAverage k n).aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableGrowthAverage_bound k hk n z)
    filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
      (ae_stableVector_growth k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz hg
    exact (hg hz.1).2
  have hlb : Tendsto (fun n => ∫ z, stableBackwardAverage k n z ∂μ) atTop
      (𝓝 (∫ z, -standardLyapunov k hk z ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ : Torus => C)
      (fun n => (measurable_stableBackwardAverage k n).aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableBackwardAverage_bound k hk n z)
      (ae_coincident_backward_growth k hk)
  have hcancel (n) : (∫ z, stableGrowthAverage k n z ∂μ) +
      (∫ z, stableBackwardAverage k n z ∂μ)=0 := by
    have hmp : MeasurePreserving ((standardMap k)^[n]) μ μ :=
      (measurePreserving_coincidentLines k hk).iterate n
    have hcomp : Integrable (fun z => stableBackwardAverage k n ((standardMap k)^[n] z)) μ :=
      hmp.integrable_comp_of_integrable (hb n)
    rw [← BoundedSubadditive.integral_comp hmp (hb n).aestronglyMeasurable,
      ← integral_add (ha n) hcomp]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
      (ae_stable_averages_cancel k hk n).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz he
    exact he hz.1
  have hz : (∫ z, -standardLyapunov k hk z ∂μ) + (∫ z, -standardLyapunov k hk z ∂μ)=0 :=
    tendsto_nhds_unique (hla.add hlb) (by simpa only [hcancel] using tendsto_const_nhds (x := (0 : ℝ)))
  have hzero : (∫ z, standardLyapunov k hk z ∂μ)=0 := by
    rw [integral_neg] at hz
    linarith
  have hAE : ∀ᵐ z ∂μ, standardLyapunov k hk z=0 :=
    (integral_eq_zero_iff_of_nonneg (standardLyapunov_nonneg k hk)
      (integrable_standardLyapunov k hk).integrableOn).mp hzero
  have hempty : ∀ᵐ z ∂μ, False := by
    filter_upwards [hAE, ae_restrict_mem (measurableSet_coincidentLines k hk)] with z hz hmem
    exact (ne_of_gt hmem.1) hz
  have hμ : μ=0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hempty)
  have hh := congrArg (fun ν : Measure Torus => ν univ) hμ
  simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hh

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma ae_transverseLines (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k z) (unstableVector k z) ≠ 0 := by
  have hh : ∀ᵐ z ∂area, z ∉ coincidentLines k hk := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using measure_coincidentLines_zero k hk
  filter_upwards [hh] with z hz hp hw
  exact hz ⟨hp,hw⟩

theorem ae_hyperbolic_splitting (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k z) (unstableVector k z) ≠ 0 ∧
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (stableVector k z) (-standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (unstableVector k z) (standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (stableVector k z) (standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (unstableVector k z) (-standardLyapunov k hk z) ∧
      wedge (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z))=0 ∧
      wedge (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z))=0 := by
  filter_upwards [ae_transverseLines k hk, ae_stableVector_growth k hk, ae_unstableVector_growth k hk,
    ae_standardLyapunov_rate k hk, ae_standardInverseLyapunov_rate k hk,
    ae_stableVector_covariant k hk, ae_unstableVector_covariant k hk] with z ht hs hu ha hb hsc huc hp
  have hrev : wedge (unstableVector k z) (stableVector k z) ≠ 0 := by
    rw [wedge_swap]; exact neg_ne_zero.mpr (ht hp)
  exact ⟨ht hp, hs hp,
    PlaneLyapunov.growth_off_line _ (standardDerivativeProduct_area k z) ha (hs hp)
      (unstableVector k z) (unstableVector_ne_zero k z) (ht hp),
    PlaneLyapunov.growth_off_line _ (standardInverseDerivativeProduct_area k z) hb (hu hp)
      (stableVector k z) (stableVector_ne_zero k z) hrev,
    hu hp, hsc hp, huc hp⟩

noncomputable def standardMap_measurableEquiv (k : ℝ) : Torus ≃ᵐ Torus where
  toFun := standardMap k
  invFun := inverseMap k
  left_inv := inverseMap_standardMap k
  right_inv := standardMap_inverseMap k
  measurable_toFun := (continuous_standardMap k).measurable
  measurable_invFun := (continuous_inverseMap k).measurable

lemma measurePreserving_inverseMap (k : ℝ) : MeasurePreserving (inverseMap k) area area :=
  (measurePreserving_standardMap k).symm (standardMap_measurableEquiv k)

lemma standardLyapunov_inverse (k : ℝ) (hk : 0≤k) (z : Torus) :
    standardLyapunov k hk (inverseMap k z)=standardLyapunov k hk z := by
  have hh := standardLyapunov_invariant k hk (inverseMap k z)
  rw [standardMap_inverseMap] at hh
  exact hh.symm

lemma standardLyapunov_inverse_iterate (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    standardLyapunov k hk ((inverseMap k)^[n] z)=standardLyapunov k hk z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', standardLyapunov_inverse, ih]

lemma inverse_covariant_line (k : ℝ) (z : Torus) {s t : ℂ}
    (h : wedge s (standardDerivative k (inverseMap k z) t)=0) :
    wedge t (standardInverseDerivative k z s)=0 := by
  have hh := (standardInverseDerivative_area k z) s (standardDerivative k (inverseMap k z) t)
  have he := standardInverseDerivative_standardDerivative k (inverseMap k z) t
  rw [standardMap_inverseMap] at he
  rw [he, h] at hh
  rw [wedge_swap, hh, neg_zero]

lemma ae_stableVector_inverse_covariant (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k (inverseMap k z)) (standardInverseDerivative k z (stableVector k z))=0 := by
  filter_upwards [(measurePreserving_inverseMap k).quasiMeasurePreserving.ae
    (ae_stableVector_covariant k hk)] with z hz hp
  apply inverse_covariant_line k z
  simpa only [standardMap_inverseMap] using hz (by simpa only [standardLyapunov_inverse] using hp)

lemma ae_unstableVector_inverse_covariant (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k (inverseMap k z)) (standardInverseDerivative k z (unstableVector k z))=0 := by
  filter_upwards [(measurePreserving_inverseMap k).quasiMeasurePreserving.ae
    (ae_unstableVector_covariant k hk)] with z hz hp
  apply inverse_covariant_line k z
  simpa only [standardMap_inverseMap] using hz (by simpa only [standardLyapunov_inverse] using hp)

lemma ae_unstableVector_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k ((standardMap k)^[n] z))
        (standardDerivativeProduct k z n (unstableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardDerivativeProduct_zero, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_unstableVector_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_unstableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_iterate] using hp)
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma ae_stableVector_inverse_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((inverseMap k)^[n] z))
        (standardInverseDerivativeProduct k z n (stableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardInverseDerivativeProduct, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_stableVector_inverse_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_inverse_iterate] using hp)
    rw [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma ae_unstableVector_inverse_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k ((inverseMap k)^[n] z))
        (standardInverseDerivativeProduct k z n (unstableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardInverseDerivativeProduct, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_unstableVector_inverse_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_unstableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_inverse_iterate] using hp)
    rw [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma invariant_unit_frame_wedge (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {s u t v : ℂ} (ht : ‖t‖=1) (hv : ‖v‖=1)
    (hst : wedge t (A s)=0) (huv : wedge v (A u)=0) :
    |wedge s u| = ‖A s‖ * ‖A u‖ * |wedge t v| := by
  have he1 := unit_collinear_eq_smul ht hst
  have he2 := unit_collinear_eq_smul hv huv
  rw [← hA, he1, he2, wedge_smul_left, wedge_smul_right, abs_mul, abs_mul,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ht, hv, mul_one, mul_one]
  ring

lemma invariant_frame_angle_rate (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s u : ℂ}
    (hs : s ≠ 0) (hu : u ≠ 0) (hw : wedge s u ≠ 0)
    (t v : ℕ → ℂ) (ht : ∀ n, ‖t n‖=1) (hv : ∀ n, ‖v n‖=1)
    (hst : ∀ n, wedge (t n) (A n s)=0) (huv : ∀ n, wedge (v n) (A n u)=0)
    {l : ℝ} (hgrs : PlaneLyapunov.Growth A s l) (hgru : PlaneLyapunov.Growth A u (-l)) :
    Tendsto (fun n : ℕ => Real.log |wedge (t n) (v n)|/(n : ℝ)) atTop (𝓝 0) := by
  have he (n) := invariant_unit_frame_wedge (A n) (hA n) (ht n) (hv n) (hst n) (huv n)
  have hpos (n) : 0 < |wedge (t n) (v n)| := by
    have hp := abs_pos.mpr hw
    rw [he n] at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (mul_nonneg (norm_nonneg _) (norm_nonneg _))) h.1) |>.2
  have ha (n) := PlaneLyapunov.image_norm_pos A hA hs n
  have hb (n) := PlaneLyapunov.image_norm_pos A hA hu n
  have hlog (n) : Real.log |wedge (t n) (v n)| =
      Real.log |wedge s u|-Real.log ‖A n s‖-Real.log ‖A n u‖ := by
    have hh := congrArg Real.log (he n)
    rw [Real.log_mul (mul_pos (ha n) (hb n)).ne' (hpos n).ne',
      Real.log_mul (ha n).ne' (hb n).ne'] at hh
    linarith
  have hc : Tendsto (fun n : ℕ => Real.log |wedge s u|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hc.sub hgrs.2).sub hgru.2
  simpa only [hlog, sub_div, zero_sub, sub_neg_eq_add, neg_add_cancel] using hh

theorem ae_angle_tempered (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      Tendsto (fun n : ℕ => Real.log |wedge (stableVector k ((standardMap k)^[n] z))
        (unstableVector k ((standardMap k)^[n] z))|/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log |wedge (stableVector k ((inverseMap k)^[n] z))
        (unstableVector k ((inverseMap k)^[n] z))|/(n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_hyperbolic_splitting k hk,
    ae_all_iff.mpr (ae_stableVector_product_covariant k hk),
    ae_all_iff.mpr (ae_unstableVector_product_covariant k hk),
    ae_all_iff.mpr (ae_stableVector_inverse_product_covariant k hk),
    ae_all_iff.mpr (ae_unstableVector_inverse_product_covariant k hk)] with z hz hsc huc hsb hub hp
  rcases hz hp with ⟨ht, hs, hu, bs, bu, _⟩
  constructor
  · apply invariant_frame_angle_rate _ (standardDerivativeProduct_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z) ht
      (fun n => stableVector k ((standardMap k)^[n] z))
      (fun n => unstableVector k ((standardMap k)^[n] z))
      (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => hsc n hp) (fun n => huc n hp) hs
    simpa only [neg_neg] using hu
  · exact invariant_frame_angle_rate _ (standardInverseDerivativeProduct_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z) ht
      (fun n => stableVector k ((inverseMap k)^[n] z))
      (fun n => unstableVector k ((inverseMap k)^[n] z))
      (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => hsb n hp) (fun n => hub n hp) bs bu

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PlaneLyapunov

noncomputable def energy (A : ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) (v : ℂ) : ℝ :=
  ∑' n : ℕ, ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ))

lemma summable_energy (A : ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ n, PlaneAreaPreserving (A n))
    {v : ℂ} {l χ : ℝ} (hg : Growth A v l) (hχ : l+χ < 0) :
    Summable (fun n : ℕ => ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ))) := by
  let a := (l-χ)/2
  have ha : l<a := by dsimp only [a]; linarith
  have hb : 2*(a+χ)<0 := by dsimp only [a]; linarith
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (2*(a+χ))).le
    (Real.exp_lt_one_iff.mpr hb)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_order.mp hg.2).2 a ha, eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hlt := (div_lt_iff₀ hnp).mp hn
  have hnorm : ‖A n v‖ ≤ Real.exp (a*(n : ℝ)) := by
    calc
      _ = Real.exp (Real.log ‖A n v‖) := (Real.exp_log (image_norm_pos A hA hg.1 n)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlt.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  calc
    _ ≤ (Real.exp (a*(n : ℝ)))^2 * Real.exp (2*χ*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le |>.mpr hnorm)
        (Real.exp_pos _).le
    _ = (Real.exp (2*(a+χ)))^n := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring

lemma energy_nonneg (A : ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) (v : ℂ) : 0 ≤ energy A χ v :=
  tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

lemma energy_ge_one (A : ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) {v : ℂ}
    (hunit : ‖v‖=1) (hzero : A 0 = ContinuousLinearMap.id ℝ ℂ)
    (hsum : Summable (fun n : ℕ => ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ)))) :
    1 ≤ energy A χ v := by
  have hh := hsum.le_tsum 0 (fun n _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  simpa only [hzero, ContinuousLinearMap.id_apply, hunit, one_pow, Nat.cast_zero,
    mul_zero, Real.exp_zero, mul_one, energy] using hh

lemma measurable_energy {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) (v : X → ℂ)
    (hA : ∀ n, Measurable (fun x => A x n)) (hv : Measurable v) :
    Measurable (fun x => energy (A x) χ (v x)) := by
  apply Measurable.tsum
  intro n
  exact (((continuous_fst.clm_apply continuous_snd :
    Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((hA n).prodMk hv)).norm.pow_const 2).mul_const _

lemma energy_shift (A B : ℕ → ℂ →L[ℝ] ℂ) (D : ℂ →L[ℝ] ℂ)
    (hshift : ∀ n v, B n (D v)=A (n+1) v)
    (hzero : A 0=ContinuousLinearMap.id ℝ ℂ) {s t : ℂ}
    (hs : ‖s‖=1) (ht : ‖t‖=1) (hcov : wedge t (D s)=0) (χ : ℝ)
    (hsum : Summable (fun n : ℕ => ‖A n s‖^2 * Real.exp (2*χ*(n : ℝ)))) :
    energy A χ s = 1 + Real.exp (2*χ)*‖D s‖^2*energy B χ t := by
  have he := unit_collinear_eq_smul ht hcov
  have hn : ‖D s‖ = |dot t (D s)| := by
    conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, ht, mul_one]
  have hc (n : ℕ) : ‖A (n+1) s‖^2 * Real.exp (2*χ*((n+1 : ℕ) : ℝ)) =
      (Real.exp (2*χ)*‖D s‖^2) * (‖B n t‖^2 * Real.exp (2*χ*(n : ℝ))) := by
    conv_lhs => rw [← hshift, he, map_smul, norm_smul, Real.norm_eq_abs, ← hn]
    have hexp : Real.exp (2*χ*((n+1 : ℕ) : ℝ)) =
        Real.exp (2*χ) * Real.exp (2*χ*(n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  unfold energy
  rw [hsum.tsum_eq_zero_add, hzero, ContinuousLinearMap.id_apply, hs, one_pow,
    Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  simp_rw [hc]
  rw [tsum_mul_left]

end PlaneLyapunov

noncomputable def stableEnergy (k χ : ℝ) (z : Torus) : ℝ :=
  PlaneLyapunov.energy (standardDerivativeProduct k z) χ (stableVector k z)
noncomputable def unstableEnergy (k χ : ℝ) (z : Torus) : ℝ :=
  PlaneLyapunov.energy (standardInverseDerivativeProduct k z) χ (unstableVector k z)

noncomputable def stableScale (k χ : ℝ) (z : Torus) : ℝ := Real.sqrt (max 1 (stableEnergy k χ z))
noncomputable def unstableScale (k χ : ℝ) (z : Torus) : ℝ := Real.sqrt (max 1 (unstableEnergy k χ z))

lemma measurable_stableEnergy (k χ : ℝ) : Measurable (stableEnergy k χ) :=
  PlaneLyapunov.measurable_energy _ χ _
    (fun n => (continuous_standardDerivativeProduct k n).measurable) (measurable_stableVector k)
lemma measurable_unstableEnergy (k χ : ℝ) : Measurable (unstableEnergy k χ) :=
  PlaneLyapunov.measurable_energy _ χ _
    (fun n => (continuous_standardInverseDerivativeProduct k n).measurable) (measurable_unstableVector k)
lemma measurable_stableScale (k χ : ℝ) : Measurable (stableScale k χ) :=
  Real.continuous_sqrt.measurable.comp (measurable_const.max (measurable_stableEnergy k χ))
lemma measurable_unstableScale (k χ : ℝ) : Measurable (unstableScale k χ) :=
  Real.continuous_sqrt.measurable.comp (measurable_const.max (measurable_unstableEnergy k χ))

lemma stableScale_ge_one (k χ : ℝ) (z : Torus) : 1 ≤ stableScale k χ z := by
  simpa only [stableScale, Real.sqrt_one] using Real.sqrt_le_sqrt (le_max_left (1 : ℝ) (stableEnergy k χ z))
lemma unstableScale_ge_one (k χ : ℝ) (z : Torus) : 1 ≤ unstableScale k χ z := by
  simpa only [unstableScale, Real.sqrt_one] using Real.sqrt_le_sqrt (le_max_left (1 : ℝ) (unstableEnergy k χ z))

lemma ae_stableEnergy_regular (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area, χ < standardLyapunov k hk z →
      Summable (fun n : ℕ => ‖standardDerivativeProduct k z n (stableVector k z)‖^2 *
        Real.exp (2*χ*(n : ℝ))) ∧ 1 ≤ stableEnergy k χ z ∧
      (stableScale k χ z)^2=stableEnergy k χ z ∧
      stableEnergy k χ z = 1 + Real.exp (2*χ)*‖standardDerivative k z (stableVector k z)‖^2*
        stableEnergy k χ (standardMap k z) := by
  filter_upwards [ae_stableVector_growth k hk, ae_stableVector_covariant k hk] with z hg hcov hpos
  have hp := hχ.trans_lt hpos
  have hsum := PlaneLyapunov.summable_energy _ (standardDerivativeProduct_area k z) (hg hp)
    (show -standardLyapunov k hk z+χ<0 by linarith)
  have hge : 1 ≤ stableEnergy k χ z := PlaneLyapunov.energy_ge_one _ χ (norm_stableVector k z) rfl hsum
  refine ⟨hsum,hge,?_,?_⟩
  · rw [stableScale, max_eq_right hge, Real.sq_sqrt (zero_le_one.trans hge)]
  · exact PlaneLyapunov.energy_shift _ _ (standardDerivative k z)
      (standardDerivativeProduct_shift k z) rfl (norm_stableVector k z)
      (norm_stableVector k _) (hcov hp) χ hsum

lemma ae_unstableEnergy_regular (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area, χ < standardLyapunov k hk z →
      Summable (fun n : ℕ => ‖standardInverseDerivativeProduct k z n (unstableVector k z)‖^2 *
        Real.exp (2*χ*(n : ℝ))) ∧ 1 ≤ unstableEnergy k χ z ∧
      (unstableScale k χ z)^2=unstableEnergy k χ z ∧
      unstableEnergy k χ z = 1 + Real.exp (2*χ)*‖standardInverseDerivative k z (unstableVector k z)‖^2*
        unstableEnergy k χ (inverseMap k z) := by
  filter_upwards [ae_unstableVector_growth k hk, ae_unstableVector_inverse_covariant k hk] with z hg hcov hpos
  have hp := hχ.trans_lt hpos
  have hsum := PlaneLyapunov.summable_energy _ (standardInverseDerivativeProduct_area k z) (hg hp)
    (show -standardLyapunov k hk z+χ<0 by linarith)
  have hge : 1 ≤ unstableEnergy k χ z := PlaneLyapunov.energy_ge_one _ χ (norm_unstableVector k z) rfl hsum
  refine ⟨hsum,hge,?_,?_⟩
  · rw [unstableScale, max_eq_right hge, Real.sq_sqrt (zero_le_one.trans hge)]
  · exact PlaneLyapunov.energy_shift _ _ (standardInverseDerivative k z)
      (standardInverseDerivativeProduct_shift k z) rfl (norm_unstableVector k z)
      (norm_unstableVector k _) (hcov hp) χ hsum

end StandardMapEntropy

end
end

end OAI
