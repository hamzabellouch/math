import OAI.Geometry.Perimeter.Regularity.PerimeterEqOfAe

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem annularCutoff_test_admissible {n : ℕ} {U : Set (Euc n)} {V : Euc n → Euc n}
    (hV : PerimeterAdmissible U V) {c : Euc n} {r a b : ℝ}
    (ha : 0 < a) (hra : r < a) (hab : a < b) :
    PerimeterAdmissible (U \ Metric.closedBall c r)
      (fun x ↦ annularCutoff c a b x • V x) := by
  have hc : HasCompactSupport V := hV.2.1
  have hcη : HasCompactSupport ((annularCutoff c a b) • V) :=
    HasCompactSupport.smul_left (f := annularCutoff c a b) hc
  refine ⟨(annularCutoff_contDiff c a b).smul hV.1, hcη, ?_, ?_⟩
  · intro x hx
    have hsV : x ∈ tsupport V := tsupport_smul_subset_right (annularCutoff c a b) V hx
    have hsη : x ∈ tsupport (annularCutoff c a b) := tsupport_smul_subset_left (annularCutoff c a b) V hx
    refine ⟨hV.2.2.1 hsV, ?_⟩
    have hax := tsupport_annularCutoff_subset ha hab hsη
    exact not_le.mpr (hra.trans_le hax)
  · intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (annularCutoff_mem_Icc c a b x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (annularCutoff_mem_Icc c a b x).2).trans (hV.2.2.2 x)

theorem integral_annularCutoff_divergence_le {n : ℕ} {E U : Set (Euc n)}
    {V : Euc n → Euc n} (hV : PerimeterAdmissible U V) {c : Euc n} {r a b L : ℝ}
    (ha : 0 < a) (hra : r < a) (hab : a < b) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hfin : perimeter E (U \ Metric.closedBall c r) ≠ ⊤) :
    (∫ x in E, annularCutoff c a b x * divergence V x) ≤
      (perimeter E (U \ Metric.closedBall c r)).toReal +
        2 * L * n * b ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1) := by
  have hη := annularCutoff_test_admissible (c := c) hV ha hra hab
  have hd := integrable_divergence hV.1 hV.2.1
  have hcd : HasCompactSupport (divergence V) :=
    hV.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset V)
  have hct : HasCompactSupport ((annularCutoff c a b) * (divergence V)) :=
    HasCompactSupport.mul_left (f := annularCutoff c a b) hcd
  have ht : Integrable (fun x ↦ annularCutoff c a b x * divergence V x) volume :=
    ((annularCutoff_contDiff c a b).continuous.mul (continuous_divergence hV.1)).integrable_of_hasCompactSupport
      hct
  have hg : Integrable (fun x ↦ ‖gradient (annularCutoff c a b) x‖) volume :=
    ((gradient_annularCutoff_continuous c a b).integrable_of_hasCompactSupport
      (gradient_annularCutoff_compact c ha hab)).norm
  have hinner : ∀ x, |inner ℝ (gradient (annularCutoff c a b) x) (V x)| ≤
      ‖gradient (annularCutoff c a b) x‖ := by
    intro x
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hV.2.2.2 x))
  have hi : Integrable (fun x ↦ inner ℝ (gradient (annularCutoff c a b) x) (V x)) volume :=
    hg.mono' ((gradient_annularCutoff_continuous c a b).inner hV.1.continuous).aestronglyMeasurable
      (Eventually.of_forall hinner)
  have hvar : (∫ x in E, divergence (fun y ↦ annularCutoff c a b y • V y) x) ≤
      (perimeter E (U \ Metric.closedBall c r)).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le _ (le_iSup_of_le hη le_rfl)
  have heq : (∫ x in E, divergence (fun y ↦ annularCutoff c a b y • V y) x) =
      (∫ x in E, annularCutoff c a b x * divergence V x) +
      (∫ x in E, inner ℝ (gradient (annularCutoff c a b) x) (V x)) := by
    simp_rw [divergence_smul ((annularCutoff_contDiff c a b).differentiable (by norm_num))
      (hV.1.differentiable (by norm_num))]
    exact integral_add ht.integrableOn hi.integrableOn
  have herr : -(∫ x in E, inner ℝ (gradient (annularCutoff c a b) x) (V x)) ≤
      ∫ x, ‖gradient (annularCutoff c a b) x‖ := by
    rw [← integral_neg]
    exact (integral_mono hi.integrableOn.neg hg.integrableOn
      (fun x ↦ (neg_le_abs _).trans (hinner x))).trans
      (setIntegral_le_integral hg (Eventually.of_forall fun x ↦ norm_nonneg _))
  have henergy := integral_gradient_annularCutoff_le c ha hab hL hbound
  linarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem annularCutoff_tendsto {n : ℕ} (c x : Euc n) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ : ℝ ↦ annularCutoff c (r + δ) (r + 2 * δ) x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Metric.closedBall c r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Metric.closedBall c r
  · rw [indicator_of_notMem (by simpa using hx)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    symm
    exact annularCutoff_zero (by simpa using add_pos hr hδ) (by linarith [show 0 < δ from hδ])
      (hx.trans (by linarith : r ≤ r + δ))
  · rw [indicator_of_mem (show x ∈ (Metric.closedBall c r)ᶜ from hx)]
    have hd : 0 < (dist x c - r) / 2 := by
      have hh : r < dist x c := lt_of_not_ge hx
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (gt_mem_nhds hd))] with δ hδ hsmall
    change 0 < δ at hδ
    symm
    exact annularCutoff_one (by simpa using add_pos hr hδ) (by linarith [show 0 < δ from hδ])
      (by change δ < (dist x c - r) / 2 at hsmall; linarith)

theorem integral_divergence_outside_le {n : ℕ} {E U : Set (Euc n)}
    {V : Euc n → Euc n} (hV : PerimeterAdmissible U V) {c : Euc n} {r L : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hfin : perimeter E (U \ Metric.closedBall c r) ≠ ⊤) :
    (∫ x in E \ Metric.closedBall c r, divergence V x) ≤
      (perimeter E (U \ Metric.closedBall c r)).toReal +
        2 * L * n * r ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1) := by
  have hd := integrable_divergence hV.1 hV.2.1
  have hlim : Tendsto (fun δ : ℝ ↦ ∫ x in E,
      annularCutoff c (r + δ) (r + 2 * δ) x * divergence V x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in E \ Metric.closedBall c r, divergence V x)) := by
    have ht := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict E) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ x ↦ annularCutoff c (r + δ) (r + 2 * δ) x * divergence V x)
      (f := (Metric.closedBall c r)ᶜ.indicator (divergence V)) (fun x ↦ ‖divergence V x‖)
      (Eventually.of_forall fun δ ↦
        ((annularCutoff_contDiff c (r + δ) (r + 2 * δ)).continuous.mul
          (continuous_divergence hV.1)).aestronglyMeasurable)
      (Eventually.of_forall fun δ ↦ Eventually.of_forall fun x ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (annularCutoff_mem_Icc c _ _ x).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (annularCutoff_mem_Icc c _ _ x).2)
      hd.norm.integrableOn (Eventually.of_forall fun x ↦ ?_)
    · simpa only [integral_indicator measurableSet_closedBall.compl,
        Measure.restrict_restrict measurableSet_closedBall.compl, inter_comm, ← Set.sdiff_eq] using ht
    · convert (annularCutoff_tendsto c x hr).mul
        (tendsto_const_nhds (x := divergence V x)) using 1
      by_cases hx : x ∈ (Metric.closedBall c r)ᶜ <;> simp [hx]
  have hpow : Tendsto (fun δ : ℝ ↦
      (perimeter E (U \ Metric.closedBall c r)).toReal +
        2 * L * n * (r + 2 * δ) ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1))
      (𝓝[>] (0 : ℝ)) (𝓝 ((perimeter E (U \ Metric.closedBall c r)).toReal +
        2 * L * n * r ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1))) := by
    have hp : ContinuousAt (fun δ : ℝ ↦
      (perimeter E (U \ Metric.closedBall c r)).toReal +
        2 * L * n * (r + 2 * δ) ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1)) 0 := by
      fun_prop
    simpa using hp.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hlim hpow
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  exact integral_annularCutoff_divergence_le hV (by simpa using add_pos hr hδ)
    (by linarith [show 0 < δ from hδ]) (by linarith [show 0 < δ from hδ]) hL hbound hfin

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem perimeter_remove_closedBall_le {n : ℕ} {E U : Set (Euc n)}
    {c : Euc n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hfin : perimeter E (U \ Metric.closedBall c r) ≠ ⊤) :
    perimeter (E \ Metric.closedBall c r) U ≤
      perimeter E (U \ Metric.closedBall c r) +
        ENNReal.ofReal (2 * L * n * r ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1)) := by
  rw [perimeter_eq_iSup_tests]
  apply iSup_le
  intro V
  apply iSup_le
  intro hV
  have h := ENNReal.ofReal_le_ofReal (integral_divergence_outside_le hV hr hL hbound hfin)
  rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hfin] at h

theorem locallyMinimizing_perimeter_growth {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {L : ℝ} (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    perimeter E (Metric.ball c r) ≤
      ENNReal.ofReal (2 * L * n * r ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1)) := by
  let U := Metric.ball c (r + 1)
  let F := E \ Metric.closedBall c r
  have hout : perimeter E (U \ Metric.closedBall c r) ≠ ⊤ :=
    ne_top_of_le_ne_top (hmin.2.1 c (r + 1) (by linarith)).ne
      (raw_perimeter_mono_region E sdiff_subset)
  have hcl : closure (symmDiff E F) ⊆ Metric.closedBall c r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hc
    rcases hx with hx | hx
    · exact hx.2 ⟨hx.1, hc⟩
    · exact hx.2 hx.1.1
  have hcp : IsCompact (closure (symmDiff E F)) :=
    (isCompact_closedBall c r).of_isClosed_subset isClosed_closure hcl
  have hcmp : perimeter E U ≤ perimeter F U :=
    hmin.2.2 c (r + 1) (by linarith) F
      (hmin.1.diff measurableSet_closedBall) hcp
      (hcl.trans (Metric.closedBall_subset_ball (by linarith)))
  have hdisj : Disjoint (Metric.ball c r) (U \ Metric.closedBall c r) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 (Metric.ball_subset_closedBall hx)
  have hsuper := perimeter_disjoint_superadditive E
    (show Metric.ball c r ⊆ U from Metric.ball_subset_ball (by linarith)) sdiff_subset hdisj
  have hremove := perimeter_remove_closedBall_le (E := E) (U := U) (c := c) hr hL hbound hout
  have htotal := hsuper.trans (hcmp.trans hremove)
  rw [add_comm (perimeter E (Metric.ball c r))] at htotal
  exact (ENNReal.add_le_add_iff_left hout).mp htotal

theorem exists_locallyMinimizing_perimeter_growth_constant (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ (c : Euc n) (r : ℝ), 0 < r →
        perimeter E (Metric.ball c r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  let C := 2 * L * n * volume.real (Metric.ball (0 : Euc n) 1)
  refine ⟨C, ?_, ?_⟩
  · unfold C
    have hv : 0 < volume.real (Metric.ball (0 : Euc n) 1) := by
      rw [measureReal_def, ENNReal.toReal_pos_iff]
      exact ⟨Metric.measure_ball_pos volume _ (by norm_num),
        (measure_mono Metric.ball_subset_closedBall).trans_lt
          (isCompact_closedBall (0 : Euc n) 1).measure_lt_top⟩
    positivity
  · intro E hmin c r hr
    convert locallyMinimizing_perimeter_growth hmin hL hbound c hr using 1
    unfold C
    congr 1
    ring

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def radialNormalTest {n : ℕ} (v x : Euc n) : Euc n :=
  (1 - Real.smoothTransition (4 * ‖x‖ ^ 2)) • v

def radialFlux {n : ℕ} (v x : Euc n) : ℝ :=
  (8 * deriv Real.smoothTransition (4 * ‖x‖ ^ 2)) * max (-inner ℝ x v) 0

theorem radialNormalTest_contDiff {n : ℕ} (v : Euc n) :
    ContDiff ℝ ∞ (radialNormalTest v) := by
  have hq : ContDiff ℝ ∞ (fun x : Euc n ↦ 4 * ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_id.norm_sq ℝ)
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp hq)).smul contDiff_const

theorem radialNormalTest_support {n : ℕ} (v : Euc n) :
    tsupport (radialNormalTest v) ⊆ Metric.closedBall 0 (1 / 2) := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hn : 1 / 2 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using h
    have hT := Real.smoothTransition.one_of_one_le (show 1 ≤ 4 * ‖x‖ ^ 2 by nlinarith)
    exact hx (by simp [radialNormalTest, hT])
  · exact Metric.isClosed_closedBall

theorem radialNormalTest_admissible {n : ℕ} {v : Euc n} (hv : ‖v‖ = 1) :
    PerimeterAdmissible (Metric.ball (0 : Euc n) 1) (radialNormalTest v) := by
  refine ⟨radialNormalTest_contDiff v,
    (isCompact_closedBall (0 : Euc n) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
      (radialNormalTest_support v),
    (radialNormalTest_support v).trans (Metric.closedBall_subset_ball (by norm_num)), ?_⟩
  intro x
  rw [radialNormalTest, norm_smul, hv, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))]
  linarith [Real.smoothTransition.nonneg (4 * ‖x‖ ^ 2)]

theorem divergence_radialNormalTest {n : ℕ} (v x : Euc n) :
    divergence (radialNormalTest v) x =
      -(8 * deriv Real.smoothTransition (4 * ‖x‖ ^ 2)) * inner ℝ x v := by
  have hq : HasFDerivAt (fun x : Euc n ↦ 4 * ‖x‖ ^ 2) ((8 : ℝ) • innerSL ℝ x) x := by
    have h0 : HasFDerivAt (fun x : Euc n ↦ ‖x‖ ^ 2) (2 • innerSL ℝ x) x := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) x).norm_sq
    simpa only [two_smul, smul_add, ← add_smul, show (4 : ℝ) + 4 = 8 by norm_num] using h0.const_mul 4
  have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable
    (by norm_num) _).hasDerivAt.comp_hasFDerivAt x hq
  have hV := ((hasFDerivAt_const (1 : ℝ) x).sub hd).smul_const v
  change HasFDerivAt (radialNormalTest v) _ x at hV
  simp only [divergence, hV.fderiv,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    zero_sub, inner_smul_right, innerSL_apply_apply,
    neg_apply, smul_eq_mul]
  calc
    _ = -(8 * deriv Real.smoothTransition (4 * ‖x‖ ^ 2)) *
        ∑ i : Fin n, inner ℝ x ((EuclideanSpace.basisFun (Fin n) ℝ) i) *
          inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [(EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner]

theorem radialFlux_eq_indicator {n : ℕ} (v x : Euc n) :
    radialFlux v x = {y | inner ℝ y v < 0}.indicator
      (divergence (radialNormalTest v)) x := by
  by_cases hx : inner ℝ x v < 0
  · rw [Set.indicator_of_mem (show x ∈ {y | inner ℝ y v < 0} from hx), divergence_radialNormalTest]
    simp only [radialFlux, max_eq_left (by linarith : 0 ≤ -inner ℝ x v)]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {y | inner ℝ y v < 0} from hx)]
    simp [radialFlux, max_eq_right (by linarith : -inner ℝ x v ≤ 0)]

theorem radialFlux_nonneg {n : ℕ} (v x : Euc n) : 0 ≤ radialFlux v x := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.smoothTransition.monotone.deriv_nonneg)
    (le_max_right _ _)

theorem radialFlux_continuous {n : ℕ} :
    Continuous (fun p : Euc n × Euc n ↦ radialFlux p.1 p.2) := by
  have hT : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by norm_num)
  exact (hT.comp ((continuous_snd.norm.pow 2).const_mul 4)).const_mul 8 |>.mul
    (((continuous_snd.inner continuous_fst).neg).max continuous_const)

theorem radialFlux_support {n : ℕ} (v : Euc n) :
    tsupport (radialFlux v) ⊆ Metric.closedBall 0 (1 / 2) := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hn : 1 / 2 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using h
    have hT := smoothTransition_deriv_zero_of_one_le (show 1 ≤ 4 * ‖x‖ ^ 2 by nlinarith)
    exact hx (by simp [radialFlux, hT])
  · exact Metric.isClosed_closedBall

theorem radialFlux_integrable {n : ℕ} (v : Euc n) : Integrable (radialFlux v) := by
  apply (radialFlux_continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact (isCompact_closedBall (0 : Euc n) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
    (radialFlux_support v)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem integral_radialFlux_pos {n : ℕ} {v : Euc n} (hv : ‖v‖ = 1) :
    0 < ∫ x, radialFlux v x := by
  obtain ⟨t, ht, hd⟩ := exists_deriv_eq_slope Real.smoothTransition (by norm_num : (0 : ℝ) < 1)
    Real.smoothTransition.continuous.continuousOn
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by norm_num)).differentiableOn
  have hd1 : deriv Real.smoothTransition t = 1 := by simpa using hd
  let x : Euc n := (-(Real.sqrt t / 2)) • v
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hnorm : ‖x‖ = Real.sqrt t / 2 := by
    simp [x, norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr)]
  have hq : 4 * ‖x‖ ^ 2 = t := by
    rw [hnorm]; nlinarith [Real.sq_sqrt ht.1.le]
  have hi : inner ℝ x v = -(Real.sqrt t / 2) := by
    simp [x, inner_smul_left, hv]
  apply (radialFlux_continuous.comp (continuous_const.prodMk continuous_id)).integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((isCompact_closedBall (0 : Euc n) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
      (radialFlux_support v)) (radialFlux_nonneg v)
  change radialFlux v x ≠ 0
  rw [radialFlux, hq, hd1, hi]
  have hm : max (- -(Real.sqrt t / 2)) 0 = Real.sqrt t / 2 := by
    simp [max_eq_left (show 0 ≤ Real.sqrt t / 2 by positivity)]
  rw [hm]
  positivity

theorem continuous_integral_radialFlux {n : ℕ} :
    Continuous (fun v : Euc n ↦ ∫ x, radialFlux v x) := by
  have heq : (fun v : Euc n ↦ ∫ x, radialFlux v x) =
      (fun v ↦ ∫ x in Metric.closedBall 0 (1 / 2), radialFlux v x) := by
    funext v
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (radialFlux_support v h)))).symm
  rw [heq]
  exact continuous_parametric_integral_of_continuous radialFlux_continuous
    (isCompact_closedBall (0 : Euc n) (1 / 2))

theorem exists_uniform_radialFlux_lower (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Euc n, ‖v‖ = 1 → c ≤ ∫ x, radialFlux v x := by
  have hne : (Metric.sphere (0 : Euc n) 1).Nonempty := by
    refine ⟨(EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩, ?_⟩
    simp
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : Euc n) 1).exists_isMinOn hne
    (continuous_integral_radialFlux (n := n)).continuousOn
  have hv1 : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
  refine ⟨∫ x, radialFlux v x, integral_radialFlux_pos hv1, fun w hw ↦ hmin ?_⟩
  simpa [Metric.mem_sphere, dist_zero_right] using hw

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def ballNormalTest {n : ℕ} (c : Euc n) (r : ℝ) (v : Euc n) (y : Euc n) : Euc n :=
  radialNormalTest v (r⁻¹ • (y - c))

theorem ballNormalTest_contDiff {n : ℕ} (c : Euc n) (r : ℝ) (v : Euc n) :
    ContDiff ℝ ∞ (ballNormalTest c r v) :=
  (radialNormalTest_contDiff v).comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem ballNormalTest_support {n : ℕ} (c : Euc n) {r : ℝ} (hr : 0 < r) (v : Euc n) :
    tsupport (ballNormalTest c r v) ⊆ Metric.closedBall c (r / 2) := by
  have hs := tsupport_comp_subset_preimage (f := fun y : Euc n ↦ r⁻¹ • (y - c)) (radialNormalTest v)
    ((continuous_id.sub continuous_const).const_smul r⁻¹)
  intro y hy
  have hmem := radialNormalTest_support v (hs hy)
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)] at hmem
  change dist y c ≤ r / 2
  rw [dist_eq_norm]
  have hm := mul_le_mul_of_nonneg_left hmem hr.le
  simpa [← mul_assoc, hr.ne', div_eq_mul_inv] using hm

theorem ballNormalTest_admissible {n : ℕ} (c : Euc n) {r : ℝ} (hr : 0 < r)
    {v : Euc n} (hv : ‖v‖ = 1) :
    PerimeterAdmissible (Metric.ball c r) (ballNormalTest c r v) := by
  refine ⟨ballNormalTest_contDiff c r v,
    (isCompact_closedBall c (r / 2)).of_isClosed_subset (isClosed_tsupport _)
      (ballNormalTest_support c hr v),
    (ballNormalTest_support c hr v).trans (Metric.closedBall_subset_ball (by linarith)), ?_⟩
  intro y
  exact (radialNormalTest_admissible hv).2.2.2 _

theorem divergence_ballNormalTest {n : ℕ} (c : Euc n) (r : ℝ) (v y : Euc n) :
    divergence (ballNormalTest c r v) y =
      r⁻¹ * divergence (radialNormalTest v) (r⁻¹ • (y - c)) := by
  have hq : HasFDerivAt (fun y : Euc n ↦ r⁻¹ • (y - c))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Euc n)) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const c).const_smul r⁻¹
  have hV := ((radialNormalTest_contDiff v).differentiable (by norm_num)
    (r⁻¹ • (y - c))).hasFDerivAt.comp y hq
  change HasFDerivAt (ballNormalTest c r v) _ y at hV
  simp only [divergence, hV.fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul,
    inner_smul_right, ← Finset.mul_sum]

theorem ballNormalTest_allIntegral {n : ℕ} (E : Set (Euc n)) (hE : MeasurableSet E) (c : Euc n)
    {r : ℝ} (hr : 0 < r) (v : Euc n) :
    (∫ y in E, divergence (ballNormalTest c r v) y) =
      ∫ y in Metric.ball c r, E.indicator (divergence (ballNormalTest c r v)) y := by
  rw [← integral_indicator (s := E)]
  · apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
    have hns : y ∉ tsupport (divergence (ballNormalTest c r v)) := fun h ↦ hy
      (((tsupport_divergence_subset _).trans (ballNormalTest_support c hr v)).trans
        (Metric.closedBall_subset_ball (show r / 2 < r by linarith)) h)
    by_cases he : y ∈ E
    · rw [Set.indicator_of_mem he, image_eq_zero_of_notMem_tsupport hns]
    · exact Set.indicator_of_notMem he _
  · exact hE

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem ballNormalTest_normalized_integral {n : ℕ} (E : Set (Euc n)) (hE : MeasurableSet E)
    (c : Euc n) {r : ℝ} (hr : 0 < r) (v : Euc n) :
    (r ^ n)⁻¹ * r * (∫ y in E, divergence (ballNormalTest c r v) y) =
      ∫ z in Metric.ball (0 : Euc n) 1,
        E.indicator (fun _ ↦ (1 : ℝ)) (c + r • z) * divergence (radialNormalTest v) z := by
  rw [ballNormalTest_allIntegral E hE c hr v]
  calc
    _ = r * ((r ^ n)⁻¹ * ∫ y in Metric.ball c r,
        E.indicator (divergence (ballNormalTest c r v)) y) := by ring
    _ = r * ∫ z in Metric.ball (0 : Euc n) 1,
        E.indicator (divergence (ballNormalTest c r v)) (c + r • z) := by
      rw [normalized_ball_integral _ _ hr]
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      by_cases he : c + r • z ∈ E
      · simp only [Set.indicator_of_mem he, one_mul, divergence_ballNormalTest,
          add_sub_cancel_left, inv_smul_smul₀ hr.ne', ← mul_assoc, mul_inv_cancel₀ hr.ne']
      · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]

theorem ballNormalTest_integral {n : ℕ} (hn : 0 < n) (E : Set (Euc n))
    (hE : MeasurableSet E) (c : Euc n) {r : ℝ} (hr : 0 < r) (v : Euc n) :
    (∫ y in E, divergence (ballNormalTest c r v) y) = r ^ (n - 1) *
      ∫ z in Metric.ball (0 : Euc n) 1,
        E.indicator (fun _ ↦ (1 : ℝ)) (c + r • z) * divergence (radialNormalTest v) z := by
  have hc := ballNormalTest_normalized_integral E hE c hr v
  have hp : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hp] at hc
  calc
    _ = r ^ (n - 1) * ((r ^ (n - 1) * r)⁻¹ * r *
        ∫ y in E, divergence (ballNormalTest c r v) y) := by field_simp
    _ = _ := by rw [hc]

end RPISingularHarnack

end

end OAI
