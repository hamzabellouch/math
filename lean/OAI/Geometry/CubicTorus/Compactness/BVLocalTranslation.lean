import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVRadial

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma norm_quotientMap_le (x : Cover) : ‖quotientMap x‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) QuotientAddGroup.norm_mk_le_norm 2

def shortestLift (x : Torus) : Cover := representative (x + quotientMap cubeCenter) - cubeCenter

lemma measurable_shortestLift : Measurable shortestLift :=
  (measurable_representative.comp (measurable_id.add_const _)).sub_const _

lemma quotientMap_shortestLift (x : Torus) : quotientMap (shortestLift x) = x := by
  simp only [shortestLift, quotientMap_sub, quotientMap_representative, add_sub_cancel_right]

lemma norm_shortestLift (x : Torus) : ‖shortestLift x‖ = ‖x‖ := by
  have hh := dist_representative_cubeCenter (x + quotientMap cubeCenter)
  simpa only [dist_eq_norm, add_sub_cancel_right, shortestLift] using hh

lemma abs_flux_local_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ x, ‖F x‖ ≤ k)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → F x = 0) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤
      k * (spatialNormalMeasure μ : Measure Torus).real B := by
  rw [← normalMeasure_flux hμ hF hp (show 0 < k + 1 by linarith)
    (fun x ↦ (hb x).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun _ ↦ k)
  have hg : Measurable g := measurable_const.indicator hB
  have hproj := integral_spatialNormalMeasure μ hg
  have hi : Integrable (fun z : NormalBundle ↦ g (normalProjection z)) (μ : Measure NormalBundle) :=
    Integrable.of_bound (hg.comp normalProjection_continuous.measurable).aestronglyMeasurable k
      (Eventually.of_forall fun z ↦ by
        by_cases hz : normalProjection z ∈ B <;> simp [g, hz, abs_of_nonneg hk, hk])
  have hb' : ∀ z : NormalBundle, ‖normalTest F hF.continuous z‖ ≤ g (normalProjection z) := by
    intro z
    by_cases hz' : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hz']
      calc
        _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := norm_inner_le_norm _ _
        _ ≤ k := by simpa only [z.2.property, one_mul] using hb z.1
    · have hf0 := hz z.1 hz'
      simp [g, hz', normalTest, hf0]
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb')
  rw [← hproj] at h
  simpa only [g, integral_indicator hB, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ, Real.norm_eq_abs, mul_comm] using h

lemma smoothApprox_zero_outside_ball {g : Cover → ℝ} {a : Torus} {r s : ℝ}
    (hz : ∀ x, quotientMap x ∉ Metric.ball a r → g x = 0) (n : ℕ)
    (hn : (mollifier n).rOut ≤ s) {x : Cover}
    (hx : quotientMap x ∉ Metric.ball a (r + s)) : smoothApprox g n x = 0 := by
  rw [smoothApprox, convolution_def]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : (mollifier n).normed volume y = 0
  · simp [hy]
  have hyn : ‖y‖ < (mollifier n).rOut := by
    have hh : y ∈ Function.support ((mollifier n).normed volume) := hy
    rw [(mollifier n).support_normed_eq] at hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hxy : quotientMap (x - y) ∉ Metric.ball a r := by
    intro hmem
    apply hx
    change dist (quotientMap x) a < r + s
    have ht := dist_triangle (quotientMap x) (quotientMap (x - y)) a
    have he : dist (quotientMap x) (quotientMap (x - y)) = ‖quotientMap y‖ := by
      rw [dist_eq_norm, quotientMap_sub, sub_sub_cancel]
    rw [he] at ht
    have hm : dist (quotientMap (x - y)) a < r := hmem
    linarith [norm_quotientMap_le y]
  simp [ContinuousLinearMap.lsmul_apply, hz (x - y) hxy]

theorem smooth_test_translation_bound_local {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)| ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖)) := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a| ≤
        ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖)) := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x • a = 0 := by
      have hm : quotientMap (x + t • a) ∉ Metric.ball c r := by
        intro hx'
        apply hx
        change dist (quotientMap x) c < r + ‖a‖
        have hh := dist_triangle (quotientMap x) (quotientMap (x + t • a)) c
        have he : dist (quotientMap x) (quotientMap (x + t • a)) = ‖quotientMap (t • a)‖ := by
          rw [dist_eq_norm, quotientMap_add, sub_add_cancel_left, norm_neg]
        rw [he] at hh
        have hs : ‖t • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg a) ht.2
        have hx'' : dist (quotientMap (x + t • a)) c < r := hx'
        linarith [norm_quotientMap_le (t • a)]
      simp [g, hz _ hm]
    have hh := abs_flux_local_bound hμ (hg.smul_const a)
      (fun n x ↦ by rw [hp']) (norm_nonneg a)
      (fun x ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg a) (hb _))
      Metric.isOpen_ball.measurableSet hzero
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ‖∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a‖ := by
      rw [← integral_integral_swap hi]
      simp_rw [hFTC, Real.norm_eq_abs]
    _ ≤ (‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖))) *
        (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact (Real.norm_eq_abs _).trans_le (ht t ht')
    _ = _ := by simp [Measure.real]

theorem measurable_test_translation_bound_local {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hn
  exact smooth_test_translation_bound_local hμ
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (fun x hx ↦ smoothApprox_zero_outside_ball hz n hn hx) a

lemma torus_test_translation_bound_local {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume| ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_translation_bound_local hμ (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) hs (fun x hx ↦ hz _ hx) a

theorem characteristic_translation_bound_local {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Torus) {r s : ℝ} (hs : 0 < s) (a : Torus) :
    (∫ x in Metric.ball c r, |characteristic E (x - a) - characteristic E x| ∂torusVolume) ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
  let d : Torus → ℝ := fun x ↦ characteristic E (x - a) - characteristic E x
  let g : Torus → ℝ := (Metric.ball c r).indicator d
  have hd : Measurable d := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hg : Measurable g := hd.indicator Metric.isOpen_ball.measurableSet
  have hbd (x) : |d x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using hbd x
    · simp [g, hx]
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_translation_bound_local hE hμ hg hb hs hz (shortestLift a)
  rw [norm_shortestLift, quotientMap_shortestLift, integral_difference_test hE hg hb] at hh
  have heq (x) : d x * g x = (Metric.ball c r).indicator (fun x ↦ |d x|) x := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
    · simp [g, hx]
  change |∫ x, d x * g x ∂torusVolume| ≤ _ at hh
  simp_rw [heq] at hh
  rw [integral_indicator Metric.isOpen_ball.measurableSet,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg (d x))] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torus_compactSpace : CompactSpace Torus :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ))).symm.compactSpace

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

theorem local_volume_product_le_perimeter {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4) :
    torusVolume.real (E ∩ Metric.ball c r) * torusVolume.real (Eᶜ ∩ Metric.ball c r) ≤
      128 * r ^ 4 * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (4 * r)) := by
  let B := Metric.ball c r
  let U := E ∩ B
  let W := Eᶜ ∩ B
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hU : MeasurableSet U := hE.inter hB
  have hW : MeasurableSet W := hE.compl.inter hB
  let f : Torus × Torus → ℝ := fun z ↦ characteristic U (z.2 - z.1) * characteristic W z.2
  have hfm : Measurable f :=
    ((measurable_characteristic hU).comp (measurable_snd.sub measurable_fst)).mul
      ((measurable_characteristic hW).comp measurable_snd)
  have hfb (z : Torus × Torus) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound U _)).trans
      (characteristic_bound W _)
  have hfi : Integrable f (torusVolume.prod torusVolume) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)
  let I : Torus → ℝ := fun a ↦ ∫ x, f (a, x) ∂torusVolume
  have hIi : Integrable I torusVolume := hfi.integral_prod_left
  have hIeq : (∫ a, I a ∂torusVolume) = torusVolume.real U * torusVolume.real W := by
    rw [show (∫ a, I a ∂torusVolume) = ∫ x, ∫ a, f (a, x) ∂torusVolume ∂torusVolume from
      integral_integral_swap hfi]
    have hinner (x : Torus) : (∫ a, f (a, x) ∂torusVolume) =
        torusVolume.real U * characteristic W x := by
      dsimp only [f]
      rw [integral_mul_const, integral_sub_left_eq_self, integral_characteristic hU.nullMeasurableSet]
      rfl
    simp_rw [hinner]
    rw [integral_const_mul, integral_characteristic hW.nullMeasurableSet]
    rfl
  have hIz (a : Torus) (ha : a ∉ Metric.ball 0 (2 * r)) : I a = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x - a ∈ U
      · have hdist : ‖a‖ < 2 * r := by
          have hh := dist_triangle x c (x - a)
          have hxB : dist x c < r := hx.2
          have hxB' : dist (x - a) c < r := hx'.2
          rw [dist_eq_norm, sub_sub_cancel] at hh
          rw [dist_comm c (x - a)] at hh
          linarith
        exact False.elim (ha (by simpa only [Metric.mem_ball, dist_zero_right] using hdist))
      · simp [f, characteristic, hx']
    · simp [f, characteristic, hx]
  let P := (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (4 * r))
  have hPn : 0 ≤ P := ENNReal.toReal_nonneg
  have hIbound (a : Torus) (ha : a ∈ Metric.ball 0 (2 * r)) : I a ≤ 2 * r * P := by
    have han : ‖a‖ < 2 * r := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    let g : Torus → ℝ := fun x ↦ |characteristic E (x - a) - characteristic E x|
    have hgm : Measurable g :=
      (((measurable_characteristic hE).comp (measurable_id.sub_const _)).sub
        (measurable_characteristic hE)).abs
    have hgb (x : Torus) : ‖g x‖ ≤ 1 := by
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
    have hgi : Integrable g torusVolume :=
      Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
    have hminor (x : Torus) : f (a, x) ≤ B.indicator g x := by
      by_cases hx : x ∈ W
      · by_cases hx' : x - a ∈ U
        · have hxE : x ∉ E := hx.1
          have hxE' : x - a ∈ E := hx'.1
          simp [f, characteristic, hx, hx', g, hx.2, hxE, hxE']
        · simp only [f, characteristic, indicator_of_notMem hx', zero_mul]
          exact indicator_nonneg (fun _ _ ↦ abs_nonneg _) _
      · simp only [f, characteristic, indicator_of_notMem hx, mul_zero]
        exact indicator_nonneg (fun _ _ ↦ abs_nonneg _) _
    have hleft : I a ≤ ∫ x in B, g x ∂torusVolume := by
      rw [← integral_indicator hB]
      apply integral_mono _ (hgi.indicator hB) hminor
      exact Integrable.of_bound (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
        (Eventually.of_forall fun x ↦ hfb (a, x))
    have htrans := characteristic_translation_bound_local hE hμ c (r := r) hr a
    have hpmono : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + r + ‖a‖)) ≤ P :=
      measureReal_mono (Metric.ball_subset_ball (by linarith))
    exact hleft.trans (htrans.trans ((mul_le_mul_of_nonneg_left hpmono (norm_nonneg a)).trans
      (mul_le_mul_of_nonneg_right han.le hPn)))
  have hir : (∫ a, I a ∂torusVolume) = ∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    by_cases ha : a ∈ Metric.ball 0 (2 * r)
    · simp [ha]
    · simp [ha, hIz a ha]
  have hbound : (∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume) ≤
      torusVolume.real (Metric.ball (0 : Torus) (2 * r)) * (2 * r * P) := by
    calc
      _ ≤ ∫ _ in Metric.ball 0 (2 * r), (2 * r * P) ∂torusVolume :=
        setIntegral_mono_on hIi.integrableOn (integrable_const _)
          Metric.isOpen_ball.measurableSet hIbound
      _ = _ := by simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hvol : torusVolume.real (Metric.ball (0 : Torus) (2 * r)) ≤ 64 * r ^ 3 := by
    rw [Measure.real_def, volume_torusBall 0 (by positivity) (by linarith),
      ENNReal.toReal_ofReal (by positivity)]
    nlinarith [Real.pi_lt_four, pow_pos hr 3]
  rw [← hIeq, hir]
  exact hbound.trans ((mul_le_mul_of_nonneg_right hvol (by positivity)).trans (by
    dsimp [P]
    ring_nf
    exact le_rfl))

theorem isMinimizerAt_perimeter_lower_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
      ∀ r : ℝ, 0 < r → r ≤ R →
        c * r ^ 2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) := by
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  refine ⟨min R 1, c ^ 2 / 2048, lt_min hR zero_lt_one, by positivity, ?_⟩
  intro μ hμ a ha r hr hrR
  have hs : 0 < r / 4 := by positivity
  have hsR : r / 4 ≤ R := by linarith [hrR.trans (min_le_left R 1)]
  have hs4 : r / 4 ≤ 1 / 4 := by linarith [hrR.trans (min_le_right R 1)]
  have hden := hd a ha (r / 4) hs hsR
  have hp := local_volume_product_le_perimeter hE hμ a hs hs4
  rw [show 4 * (r / 4) = r by ring] at hp
  have hprod := mul_le_mul hden.1 hden.2 (by positivity : 0 ≤ c * (r / 4) ^ 3)
    ENNReal.toReal_nonneg
  have hh := hprod.trans hp
  have hr4 : 0 < r ^ 4 := pow_pos hr _
  have hmul : 0 ≤ ((spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) -
      c ^ 2 / 2048 * r ^ 2) * r ^ 4 := by nlinarith [hh]
  have := nonneg_of_mul_nonneg_left hmul hr4
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def reverseNormal (z : NormalBundle) : NormalBundle :=
  (z.1, ⟨-(z.2 : Cover), by simpa only [norm_neg] using z.2.property⟩)

lemma continuous_reverseNormal : Continuous reverseNormal := by
  exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

lemma isNormalMeasure_compl {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure Eᶜ (μ.map reverseNormal) := by
  constructor
  · have hm : ((μ.map reverseNormal).mass : ℝ) = (μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal
        (Measure.map_apply continuous_reverseNormal.measurable MeasurableSet.univ
          (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ, FiniteMeasure.mass, FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map, Measure.real, ENNReal.toReal] using hh
    rw [hm, hμ.1, perimeter_compl hE.nullMeasurableSet]
  · intro F hF
    change (∫ z, normalTest F hF.1.continuous z
      ∂Measure.map reverseNormal (μ : Measure NormalBundle)) = _
    rw [integral_map continuous_reverseNormal.measurable.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable]
    change (∫ z, ⟪-(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
    simp_rw [inner_neg_left, integral_neg]
    rw [integral_divergence_compl hE.nullMeasurableSet hF, ← hμ.2 F hF]
    rfl

lemma spatialNormalMeasure_reverse (μ : FiniteMeasure NormalBundle) :
    spatialNormalMeasure (μ.map reverseNormal) = spatialNormalMeasure μ := by
  apply Subtype.ext
  change Measure.map normalProjection (Measure.map reverseNormal (μ : Measure NormalBundle)) = _
  rw [Measure.map_map normalProjection_continuous.measurable continuous_reverseNormal.measurable]
  rfl

lemma perimeter_eq_zero_of_volume_eq_zero {E : Set Torus} (hE : torusVolume E = 0) :
    perimeter E = 0 := by
  rw [perimeter_congr_ae (ae_eq_empty.mpr hE), perimeter_empty]

lemma spatialNormalMeasure_support_subset_volumeSupport {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E := by
  intro a ha
  rw [mem_volumeSupport_iff]
  intro r hr
  by_contra! hv
  have hz : torusVolume (E ∩ Metric.ball a r) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hv ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  let s := min r (1 / 4 : ℝ)
  have hs : 0 < s := lt_min hr (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsr : s ≤ r := min_le_left _ _
  have hcut : perimeter (E ∩ sublevelRegion (localRadialSquared a) (s ^ 2)) = 0 := by
    rw [sublevelRegion_localRadialSquared a hs.le hs4]
    apply perimeter_eq_zero_of_volume_eq_zero
    apply measure_mono_null (inter_subset_inter_right E (Metric.ball_subset_ball hsr)) hz
  have hbound := spatialNormalMeasure_sublevel_le hE hμ (localRadialSquared_contDiff a)
    (localRadialSquared_periodic a) (s := (s / 2) ^ 2) (t := s ^ 2)
    (by nlinarith [sq_pos_of_pos hs]) (by rw [hcut]; exact ENNReal.zero_ne_top)
  rw [hcut, ENNReal.toReal_zero,
    sublevelRegion_localRadialSquared a (by positivity : 0 ≤ s / 2) (by linarith)] at hbound
  have hzero : (spatialNormalMeasure μ : Measure Torus) (Metric.ball a (s / 2)) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hbound ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  have hp := (Metric.nhds_basis_ball.mem_measureSupport.mp ha) (s / 2) (by positivity)
  exact hp.ne' hzero

lemma spatialNormalMeasure_support_subset_boundary {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E ∩ volumeSupport Eᶜ := by
  intro a ha
  refine ⟨spatialNormalMeasure_support_subset_volumeSupport hE hμ ha, ?_⟩
  have hh := spatialNormalMeasure_support_subset_volumeSupport hE.compl (isNormalMeasure_compl hE hμ)
  rw [spatialNormalMeasure_reverse] at hh
  exact hh ha

theorem isMinimizerAt_perimeter_support {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support = frontier (openRepresentative E) := by
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  apply subset_antisymm (spatialNormalMeasure_support_subset_boundary hE hμ)
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  intro a ha
  rw [Metric.nhds_basis_ball.mem_measureSupport]
  intro r hr
  have hs : 0 < min R r := lt_min hR hr
  have hh := hd μ hμ a ha (min R r) hs (min_le_left _ _)
  have hp : 0 < (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) :=
    (by positivity : 0 < c * (min R r) ^ 2).trans_le
      (hh.trans (measureReal_mono (Metric.ball_subset_ball (min_le_right _ _))))
  exact (ENNReal.toReal_pos_iff.mp hp).1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

def supportedMeasure (σ : FiniteMeasure Torus) : Measure (σ : Measure Torus).support :=
  Measure.comap Subtype.val (σ : Measure Torus)

instance supportedMeasure_finite (σ : FiniteMeasure Torus) : IsFiniteMeasure (supportedMeasure σ) :=
  inferInstanceAs (IsFiniteMeasure (Measure.comap _ (σ : Measure Torus)))

lemma map_supportedMeasure (σ : FiniteMeasure Torus) :
    Measure.map Subtype.val (supportedMeasure σ) = (σ : Measure Torus) := by
  rw [supportedMeasure, map_comap_subtype_coe Measure.isClosed_support.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (Measure.support_mem_ae (μ := (σ : Measure Torus)))

lemma supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) :
    supportedMeasure σ (Metric.closedBall a r) =
      (σ : Measure Torus) (Metric.closedBall (a : Torus) r) := by
  have hh := Measure.map_apply (μ := supportedMeasure σ) measurable_subtype_coe
    (show MeasurableSet (Metric.closedBall (a : Torus) r) from Metric.isClosed_closedBall.measurableSet)
  rw [map_supportedMeasure σ] at hh
  exact hh.symm

lemma setIntegral_supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) (f : Torus → ℝ) :
    (∫ x in Metric.closedBall a r, f (x : Torus) ∂supportedMeasure σ) =
      ∫ x in Metric.closedBall (a : Torus) r, f x ∂(σ : Measure Torus) := by
  have hh := (MeasurableEmbedding.subtype_coe
    (Measure.isClosed_support (μ := (σ : Measure Torus))).measurableSet).setIntegral_map
    (μ := supportedMeasure σ) f (Metric.closedBall (a : Torus) r)
  rw [map_supportedMeasure σ] at hh
  exact hh.symm

lemma setAverage_supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) (f : Torus → ℝ) :
    (⨍ x in Metric.closedBall a r, f (x : Torus) ∂supportedMeasure σ) =
      ⨍ x in Metric.closedBall (a : Torus) r, f x ∂(σ : Measure Torus) := by
  simp only [setAverage_eq, Measure.real_def, supportedMeasure_closedBall,
    setIntegral_supportedMeasure_closedBall]

theorem isMinimizerAt_supportedMeasure_doubling {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsUnifLocDoublingMeasure (supportedMeasure (spatialNormalMeasure μ)) := by
  obtain ⟨R₁, A, hR₁, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨R₂, c, hR₂, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let σ := spatialNormalMeasure μ
  let C : ℝ≥0 := ⟨9 * A / c, by positivity⟩
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show 0 < min (R₁ / 3) R₂ by positivity))]
    with r hr hrR a
  have hrpos : 0 < r := hr
  change r < min (R₁ / 3) R₂ at hrR
  have hru : 3 * r ≤ R₁ := by linarith [(lt_min_iff.mp hrR).1]
  have hrl : r ≤ R₂ := (lt_min_iff.mp hrR).2.le
  have ha : (a : Torus) ∈ volumeSupport E ∩ volumeSupport Eᶜ :=
    spatialNormalMeasure_support_subset_boundary hE hμ a.property
  have hupper := hu μ hμ (a : Torus) (3 * r) (by positivity) hru
  have hlower := hl μ hμ (a : Torus) ha r hrpos hrl
  have hub := (measureReal_mono
    (Metric.closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans hupper
  have hlb := hlower.trans (measureReal_mono Metric.ball_subset_closedBall)
  rw [supportedMeasure_closedBall, supportedMeasure_closedBall]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (σ : Measure Torus).real (Metric.closedBall (a : Torus) (2 * r)) ≤
    (9 * A / c) * (σ : Measure Torus).real (Metric.closedBall (a : Torus) r)
  have hh := mul_le_mul_of_nonneg_left hlb (show 0 ≤ 9 * A / c by positivity)
  have he : (9 * A / c) * (c * r ^ 2) = A * (3 * r) ^ 2 := by field_simp; ring
  rw [he] at hh
  exact hub.trans hh

theorem isMinimizerAt_normal_differentiation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hb : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ ≤ 1) :
    ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, ‖N x - N a‖
        ∂(spatialNormalMeasure μ : Measure Torus)) (𝓝[>] 0) (𝓝 0) := by
  let σ := spatialNormalMeasure μ
  let ν := supportedMeasure σ
  let := isMinimizerAt_supportedMeasure_doubling hV hE hmin hμ
  have hb' : ∀ᵐ (x : (σ : Measure Torus).support) ∂ν, ‖N (x : Torus)‖ ≤ 1 := by
    rw [← map_supportedMeasure σ,
      (MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet).ae_map_iff] at hb
    exact hb
  have hi : Integrable (fun x : (σ : Measure Torus).support ↦ N (x : Torus)) ν :=
    Integrable.of_bound (hN.comp measurable_subtype_coe).aestronglyMeasurable 1 hb'
  have hd := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub ν hi.locallyIntegrable 1
  have hh : ∀ᵐ a ∂Measure.map Subtype.val ν,
      Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, ‖N x - N a‖ ∂(σ : Measure Torus))
        (𝓝[>] 0) (𝓝 0) := by
    rw [(MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet).ae_map_iff]
    filter_upwards [hd] with a ha
    have hh := ha (fun _ : ℝ ↦ a) id tendsto_id
      (show ∀ᶠ r : ℝ in 𝓝[>] 0, a ∈ Metric.closedBall a (1 * id r) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact Metric.mem_closedBall_self (by simpa using le_of_lt hr))
    exact hh.congr' (Eventually.of_forall fun r ↦
      setAverage_supportedMeasure_closedBall σ a r (fun x ↦ ‖N x - N (a : Torus)‖))
  simpa only [ν, map_supportedMeasure] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma normalMeasure_polar_unit {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) :
    ∃ N : Torus → Cover, Measurable N ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) ∧
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) := by
  obtain ⟨N, hN, hp⟩ := normalMeasure_exists_polar hμ
  refine ⟨N, hN, hp, ?_⟩
  change ∀ᵐ x ∂Measure.map normalProjection (μ : Measure NormalBundle), ‖N x‖ = 1
  rw [ae_map_iff normalProjection_continuous.measurable.aemeasurable
    (measurableSet_eq_fun hN.norm measurable_const)]
  filter_upwards [hp] with z hz
  change ‖N (quotientMap z.1)‖ = 1
  rw [hz, z.2.property]

def normalExcess (σ : FiniteMeasure Torus) (N : Torus → Cover) (a : Torus)
    (n : Cover) (r : ℝ) : ℝ :=
  (∫ x in Metric.closedBall a r, ‖N x - n‖ ^ 2 ∂(σ : Measure Torus)) / r ^ 2

theorem isMinimizerAt_normal_excess_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus), ‖N a‖ = 1 ∧
      Tendsto (normalExcess (spatialNormalMeasure μ) N a (N a)) (𝓝[>] 0) (𝓝 0) := by
  let σ := spatialNormalMeasure μ
  obtain ⟨R, A, hR, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have havg := isMinimizerAt_normal_differentiation hV hE hmin hμ hN
    (hn.mono fun _ hx ↦ hx.le)
  filter_upwards [havg, hn, (Measure.support_mem_ae (μ := (σ : Measure Torus)))] with a ha hna has
  refine ⟨hna, ?_⟩
  have hi : Integrable (fun x ↦ ‖N x - N a‖) (σ : Measure Torus) := by
    apply Integrable.of_bound (hN.sub_const _).norm.aestronglyMeasurable 2
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [hx, hna, one_add_one_eq_two] using norm_sub_le (N x) (N a)
  have hisq : Integrable (fun x ↦ ‖N x - N a‖ ^ 2) (σ : Measure Torus) := by
    apply Integrable.of_bound ((hN.sub_const _).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hh : ‖N x - N a‖ ≤ 2 := by simpa only [hx, hna, one_add_one_eq_two] using norm_sub_le (N x) (N a)
    nlinarith [norm_nonneg (N x - N a)]
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] 0,
      normalExcess σ N a (N a) r ≤
        (8 * A) * (⨍ x in Metric.closedBall a r, ‖N x - N a‖ ∂(σ : Measure Torus)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show 0 < R / 2 by positivity))] with r hr hrR
    have hrpos : 0 < r := hr
    have hrlt : r < R / 2 := hrR
    have hm : 0 < (σ : Measure Torus).real (Metric.closedBall a r) := by
      apply ENNReal.toReal_pos
      · exact ne_of_gt (((Metric.nhds_basis_ball.mem_measureSupport.mp has) r hrpos).trans_le
          (measure_mono Metric.ball_subset_closedBall))
      · exact measure_ne_top _ _
    have hup := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : r < 2 * r))).trans
      (hu μ hμ a (2 * r) (by positivity) (by linarith : 2 * r ≤ R))
    have hsquared : (∫ x in Metric.closedBall a r, ‖N x - N a‖ ^ 2 ∂(σ : Measure Torus)) ≤
        2 * (∫ x in Metric.closedBall a r, ‖N x - N a‖ ∂(σ : Measure Torus)) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hisq.integrableOn (hi.const_mul 2).integrableOn
      filter_upwards [ae_restrict_of_ae hn] with x hx
      have hh : ‖N x - N a‖ ≤ 2 := by simpa only [hx, hna, one_add_one_eq_two] using norm_sub_le (N x) (N a)
      nlinarith [norm_nonneg (N x - N a)]
    have hi0 : 0 ≤ ∫ x in Metric.closedBall a r, ‖N x - N a‖ ∂(σ : Measure Torus) :=
      integral_nonneg fun _ ↦ norm_nonneg _
    dsimp only [normalExcess]
    rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul]
    apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).2
    have hh := mul_le_mul_of_nonneg_right hup hi0
    have hh' := mul_le_mul_of_nonneg_right hsquared hm.le
    nlinarith
  have hlo : ∀ r : ℝ, 0 ≤ normalExcess σ N a (N a) r := by
    intro r
    exact div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _)
  exact squeeze_zero' (Eventually.of_forall hlo) hbound (by
    simpa only [mul_zero] using ha.const_mul (8 * A))

theorem isMinimizerAt_exists_unit_normal_excess {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ N : Torus → Cover, Measurable N ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) ∧
      ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus), ‖N a‖ = 1 ∧
        Tendsto (normalExcess (spatialNormalMeasure μ) N a (N a)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨N, hN, hp, hn⟩ := normalMeasure_polar_unit hμ
  exact ⟨N, hN, hp, isMinimizerAt_normal_excess_ae hV hE hmin hμ hN hn⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

def directionalMass (σ : FiniteMeasure Torus) (N : Torus → Cover)
    (a : Cover) (B : Set Torus) : ℝ :=
  ∫ x in B, |⟪N x, a⟫| ∂(σ : Measure Torus)

lemma directionalMass_nonneg (σ : FiniteMeasure Torus) (N : Torus → Cover)
    (a : Cover) (B : Set Torus) : 0 ≤ directionalMass σ N a B :=
  integral_nonneg fun _ ↦ abs_nonneg _

lemma directionalMass_integrable {σ : FiniteMeasure Torus} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (a : Cover) :
    Integrable (fun x ↦ |⟪N x, a⟫|) (σ : Measure Torus) := by
  apply Integrable.of_bound (hN.inner measurable_const).abs.aestronglyMeasurable ‖a‖
  filter_upwards [hn] with x hx
  simpa only [Real.norm_eq_abs, abs_abs, hx, one_mul] using abs_real_inner_le_norm (N x) a

lemma abs_flux_directional_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → f x = 0)
    (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun x ↦ f x • a) x| ≤
      directionalMass (spatialNormalMeasure μ) N a B := by
  have hfa := hf.smul_const a
  rw [← normalMeasure_flux hμ hfa (fun n x ↦ by rw [hp])
    (show 0 < ‖a‖ + 1 by positivity) (fun x ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg a) (hb x)).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun x ↦ |⟪N x, a⟫|)
  have hg : Measurable g := (hN.inner measurable_const).abs.indicator hB
  have hi : Integrable g (spatialNormalMeasure μ : Measure Torus) :=
    (directionalMass_integrable hN hn a).indicator hB
  have him : Integrable (fun z : NormalBundle ↦ g (normalProjection z))
      (μ : Measure NormalBundle) := by
    exact (integrable_map_measure hg.aestronglyMeasurable
      normalProjection_continuous.measurable.aemeasurable).mp hi
  have hb' : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖normalTest (fun x ↦ f x • a) hfa.continuous z‖ ≤ g (normalProjection z) := by
    filter_upwards [hpolar] with z hz'
    by_cases hzB : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hzB, normalTest, ContinuousMap.coe_mk,
        real_inner_smul_right, Real.norm_eq_abs, abs_mul]
      change |f z.1| * |⟪(z.2 : Cover), a⟫| ≤ |⟪N (quotientMap z.1), a⟫|
      rw [hz']
      exact mul_le_of_le_one_left (abs_nonneg _) (hb _)
    · simp [g, hzB, normalTest, hz z.1 hzB]
  have hh := norm_integral_le_of_norm_le him hb'
  rw [← integral_spatialNormalMeasure μ hg] at hh
  simpa only [g, integral_indicator hB, Real.norm_eq_abs, directionalMass] using hh

theorem smooth_test_directional_translation_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)| ≤
      directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + ‖a‖)) := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a| ≤
        directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + ‖a‖)) := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x = 0 := by
      have hm : quotientMap (x + t • a) ∉ Metric.ball c r := by
        intro hx'
        apply hx
        change dist (quotientMap x) c < r + ‖a‖
        have hh := dist_triangle (quotientMap x) (quotientMap (x + t • a)) c
        have he : dist (quotientMap x) (quotientMap (x + t • a)) = ‖quotientMap (t • a)‖ := by
          rw [dist_eq_norm, quotientMap_add, sub_add_cancel_left, norm_neg]
        rw [he] at hh
        have hs : ‖t • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg a) ht.2
        have hx'' : dist (quotientMap (x + t • a)) c < r := hx'
        linarith [norm_quotientMap_le (t • a)]
      simp [g, hz _ hm]
    have hh := abs_flux_directional_bound hμ hN hpolar hn hg hp' (fun x ↦ hb _)
      Metric.isOpen_ball.measurableSet hzero a
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ‖∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a‖ := by
      rw [← integral_integral_swap hi]
      simp_rw [hFTC, Real.norm_eq_abs]
    _ ≤ (directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + ‖a‖))) *
        (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact (Real.norm_eq_abs _).trans_le (ht t ht')
    _ = _ := by simp [Measure.real]

theorem measurable_test_directional_translation_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + s + ‖a‖)) := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hnr
  exact smooth_test_directional_translation_bound hμ hN hpolar hn
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (fun x hx ↦ smoothApprox_zero_outside_ball hz n hnr hx) a

lemma torus_test_directional_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume| ≤
      directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + s + ‖a‖)) := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_directional_translation_bound hμ hN hpolar hn (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) hs (fun x hx ↦ hz _ hx) a

theorem characteristic_directional_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : Torus) {r s : ℝ} (hs : 0 < s) (a : Cover) :
    (∫ x in Metric.ball c r, |characteristic E (x - quotientMap a) - characteristic E x| ∂torusVolume) ≤
      directionalMass (spatialNormalMeasure μ) N a (Metric.ball c (r + s + ‖a‖)) := by
  let d : Torus → ℝ := fun x ↦ characteristic E (x - quotientMap a) - characteristic E x
  let g : Torus → ℝ := (Metric.ball c r).indicator d
  have hd : Measurable d := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hg : Measurable g := hd.indicator Metric.isOpen_ball.measurableSet
  have hbd (x) : |d x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using hbd x
    · simp [g, hx]
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_directional_translation_bound hE hμ hN hpolar hn hg hb hs hz a
  rw [integral_difference_test hE hg hb] at hh
  have heq (x) : d x * g x = (Metric.ball c r).indicator (fun x ↦ |d x|) x := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
    · simp [g, hx]
  change |∫ x, d x * g x ∂torusVolume| ≤ _ at hh
  simp_rw [heq] at hh
  rw [integral_indicator Metric.isOpen_ball.measurableSet,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg (d x))] at hh
  exact hh

end CubicTorus

end
end

end

end OAI
