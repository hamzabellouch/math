import OAI.Analysis.IntegralMeans.CriticalMap

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma second_derivative_nonneg_at_min_zero {f f' : ℝ → ℝ} {b : ℝ}
    (hmin : IsLocalMin f 0) (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' b 0) : 0 ≤ b := by
  by_contra hb
  have hb : b < 0 := lt_of_not_ge hb
  have hzero : f' 0 = 0 := hmin.hasDerivAt_eq_zero hf.self_of_nhds
  have hrem := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf').bound
    (by linarith : 0 < -b/2)
  have he : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt f (f' x) x ∧ f 0 ≤ f x ∧ |f' x - x*b| ≤ (-b/2)*|x| := by
    filter_upwards [hf,hmin,hrem] with x hdx hmx hrx
    exact ⟨hdx,hmx,by simpa [hzero,Real.norm_eq_abs] using hrx⟩
  obtain ⟨δ,hδ,hall⟩ := Metric.eventually_nhds_iff.mp he
  have hball {x : ℝ} (hx : x ∈ Icc 0 (δ/2)) : dist x 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  have hc : ContinuousOn f (Icc 0 (δ/2)) := by
    intro x hx
    exact (hall (hball hx)).1.continuousAt.continuousWithinAt
  obtain ⟨c,hcint,hceq⟩ := exists_deriv_eq_slope f (by linarith : 0 < δ/2) hc
    (fun x hx => (hall (hball (Ioo_subset_Icc_self hx))).1.differentiableAt.differentiableWithinAt)
  have hcl := hall (hball (Ioo_subset_Icc_self hcint))
  rw [hcl.1.deriv] at hceq
  have hend := (hall (hball (show δ/2 ∈ Icc 0 (δ/2) by constructor <;> linarith))).2.1
  have hf'c : 0 ≤ f' c := by
    rw [hceq]
    exact div_nonneg (sub_nonneg.mpr hend) (by linarith)
  have hupper := (le_abs_self (f' c-c*b)).trans hcl.2.2
  rw [abs_of_pos hcint.1] at hupper
  nlinarith [mul_neg_of_pos_of_neg hcint.1 hb]

lemma second_directional_nonneg_at_min {u : ℂ → ℝ} {z v : ℂ}
    (hmin : IsLocalMin u z)
    (hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ u w)
    (hv : DifferentiableAt ℝ (fun w => fderiv ℝ u w v) z) :
    0 ≤ fderiv ℝ (fun w => fderiv ℝ u w v) z v := by
  let g : ℝ → ℂ := fun t => z + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
    simpa [g] using (hasDerivAt_id t).smul_const v |>.const_add z
  have hgz : g 0 = z := by simp [g]
  have hmin' : IsLocalMin (u ∘ g) 0 :=
    (hgz ▸ hmin).comp_continuous (hg 0).continuousAt
  have hu' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (u ∘ g) (fderiv ℝ u (g t) v) t := by
    have ht : Tendsto g (𝓝 0) (𝓝 z) := hgz ▸ (hg 0).continuousAt
    filter_upwards [ht.eventually hu] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hg t)
  have hv' : HasDerivAt (fun t => fderiv ℝ u (g t) v)
      (fderiv ℝ (fun w => fderiv ℝ u w v) z v) 0 := by
    exact (hv.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hg 0) hgz.symm)
  exact second_derivative_nonneg_at_min_zero hmin' hu' hv'

lemma differentiableAt_fderiv_logPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ (logPotential f k ξ) w v) z := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w v) =ᶠ[𝓝 z]
      (fun w => k / w.im * v.im - (targetRatio f ξ w * v).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne]
    unfold targetRatio
    congr 2
    ring
  have ha : DifferentiableAt ℝ (fun w : ℂ => k / w.im * v.im) z := by
    have hi := (hasDerivAt_inv (ne_of_gt hz)).differentiableAt.comp z
      Complex.imCLM.differentiableAt
    simpa only [div_eq_mul_inv, Function.comp_def, Complex.imCLM_apply] using
      (hi.const_mul k).mul_const v.im
  have hb : DifferentiableAt ℝ (fun w => (targetRatio f ξ w * v).re) z :=
    Complex.reCLM.differentiableAt.comp z
      (((hasDerivAt_targetRatio hf hz hp).differentiableAt.restrictScalars ℝ).mul_const v)
  exact (ha.sub hb).congr_of_eventuallyEq heq

lemma not_isLocalMin_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    ¬ IsLocalMin (logPotential f k ξ) z := by
  intro hmin
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (logPotential f k ξ) w := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hd.continuousAt.eventually_ne hp]
      with w hw hne
    exact differentiableAt_logPotential hf hw hne k
  have h1 := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k 1)
  have hI := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k Complex.I)
  have ht := trace_realHessian_negative hf hk hz hp
  simp only [realHessian, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  change secondDirectional _ z 1 1 + secondDirectional _ z Complex.I Complex.I < 0 at ht
  unfold secondDirectional at ht
  linarith

def reciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z-ξ‖ / z.im^k

lemma continuousOn_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    (k : ℝ) (ξ : ℂ) : ContinuousOn (reciprocalPotential f k ξ) halfPlane := by
  apply ((hf.1.continuousOn.sub continuousOn_const).norm).div
    (Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt hz)))
  intro z hz
  exact ne_of_gt (Real.rpow_pos_of_pos hz k)

lemma reciprocalPotential_pos {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) : 0 < reciprocalPotential f k ξ z := by
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp)) (Real.rpow_pos_of_pos hz k)

lemma log_reciprocalPotential {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    Real.log (reciprocalPotential f k ξ z) = -logPotential f k ξ z := by
  rw [reciprocalPotential,Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
    (ne_of_gt (Real.rpow_pos_of_pos hz k)),Real.log_rpow hz,logPotential]
  ring

lemma not_isLocalMax_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    ¬ IsLocalMax (reciprocalPotential f k ξ) z := by
  intro hmax
  apply not_isLocalMin_logPotential hf hk hz hp
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  filter_upwards [hmax,isOpen_halfPlane.mem_nhds hz,hd.continuousAt.eventually_ne hp]
    with w hw hwH hwne
  have hl := Real.log_le_log (reciprocalPotential_pos hwH hwne) hw
  rw [log_reciprocalPotential hwH hwne,log_reciprocalPotential hz hp] at hl
  linarith

lemma reciprocalPotential_lt_boundary {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ) {U : Set ℂ}
    (ho : IsOpen U) (hcompact : IsCompact (closure U))
    (hH : closure U ⊆ halfPlane)
    (hboundary : ∀ z ∈ frontier U, reciprocalPotential f k ξ z ≤ b)
    {z : ℂ} (hz : z ∈ U) : reciprocalPotential f k ξ z < b := by
  have hcont := (continuousOn_reciprocalPotential hf k ξ).mono hH
  obtain ⟨a,ha,hmax⟩ := hcompact.exists_isMaxOn ⟨z,subset_closure hz⟩ hcont
  have hmaxle : reciprocalPotential f k ξ a ≤ b := by
    by_contra hn
    have hab : b < reciprocalPotential f k ξ a := lt_of_not_ge hn
    have haU : a ∈ U := by
      by_contra hau
      have haf : a ∈ frontier U := ⟨ha,by simpa only [ho.interior_eq] using hau⟩
      exact (not_lt_of_ge (hboundary a haf)) hab
    have hane : f a ≠ ξ := by
      intro he
      have he0 : reciprocalPotential f k ξ a = 0 := by simp [reciprocalPotential,he]
      linarith
    exact not_isLocalMax_reciprocalPotential hf hk (hH ha) hane
      (hmax.isLocalMax (mem_of_superset (ho.mem_nhds haU) subset_closure))
  have hwhole : ∀ w ∈ closure U, reciprocalPotential f k ξ w ≤ b :=
    fun w hw => (hmax hw).trans hmaxle
  have hzle := hwhole z (subset_closure hz)
  apply lt_of_le_of_ne hzle
  intro he
  have hzne : f z ≠ ξ := by
    intro hze
    have he0 : reciprocalPotential f k ξ z = 0 := by simp [reciprocalPotential,hze]
    linarith
  apply not_isLocalMax_reciprocalPotential hf hk (hH (subset_closure hz)) hzne
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (hwhole w (subset_closure hw)).trans_eq he.symm

def regularizedGradient (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℂ :=
  ((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)*conj (criticalMap f k z-ξ)

lemma regularizedGradient_eq_zero_iff {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    regularizedGradient f k ξ z = 0 ↔ f z = ξ ∨ criticalMap f k z = ξ := by
  have hc : ((k : ℂ)*Complex.I/(z.im : ℂ)) ≠ 0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))
  simp only [regularizedGradient,mul_eq_zero,hc,false_or,sub_eq_zero,map_eq_zero]

lemma differentiableAt_gradientCoefficient {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) :
    DifferentiableAt ℝ (fun w : ℂ => (k : ℂ)*Complex.I/(w.im : ℂ)) z := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := ((hasDerivAt_inv hn).differentiableAt.restrictScalars ℝ).comp z
    ((Complex.ofRealCLM.comp Complex.imCLM).differentiableAt)
  simpa only [div_eq_mul_inv,Function.comp_def,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.imCLM_apply] using hi.const_mul ((k : ℂ)*Complex.I)

lemma differentiableAt_regularizedGradient {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (ξ : ℂ) :
    DifferentiableAt ℝ (regularizedGradient f k ξ) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  exact ((differentiableAt_gradientCoefficient hz k).mul (hd.sub_const ξ)).mul
    (Complex.conjCLE.differentiableAt.comp z ((differentiableAt_criticalMap hf hz k).sub_const ξ))

lemma hasFDerivAt_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)) •
        (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (criticalMap f k) z))) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def, hc, sub_self, map_zero, zero_smul, add_zero]

lemma hasFDerivAt_regularizedGradient_at_pole {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane)
    (hp : f z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ)*Complex.I/(z.im : ℂ))*conj (criticalMap f k z-ξ)) •
        (fderiv ℝ f z)) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def, hp, sub_self, mul_zero, zero_smul, zero_add, add_zero, smul_smul, Complex.conjCLE_apply, mul_comm]

lemma det_conj_comp (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (Complex.conjCLE.toContinuousLinearMap.comp A).toLinearMap =
      -LinearMap.det A.toLinearMap := by
  rw [determinant_complex_real,determinant_complex_real]
  simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,Complex.conj_re,Complex.conj_im]
  ring

lemma det_regularizedGradient_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane) (hc : criticalMap f k z = ξ) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap =
      -‖((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2 *
        normalizedJacobian f k z := by
  rw [(hasFDerivAt_regularizedGradient_at_critical hf hz hc).fderiv,
    det_complex_smul,det_conj_comp,normalizedJacobian]
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  field_simp

lemma det_regularizedGradient_at_pole_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {ξ z : ℂ} (hz : z ∈ halfPlane) (hp : f z = ξ) :
    0 < LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap := by
  have hG : criticalMap f k z ≠ ξ := fun hc => criticalMap_ne_pole hf hk hz hc hp
  rw [(hasFDerivAt_regularizedGradient_at_pole hf hz hp).fderiv,det_complex_smul,
    det_fderiv_complex ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz))]
  apply mul_pos
  · apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact mul_ne_zero (div_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
      ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hG))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf hz))

end Brennan

end

end OAI
