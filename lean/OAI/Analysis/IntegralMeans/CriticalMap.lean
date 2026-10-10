import OAI.Analysis.IntegralMeans.HalfPlane

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

def logarithmicJet (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * (z.im : ℂ) * deriv (reciprocalDeriv f) z / reciprocalDeriv f z

lemma logarithmicJet_eq {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    logarithmicJet f z = -Complex.I * (z.im : ℂ) * deriv (deriv f) z / deriv f z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hq : deriv (reciprocalDeriv f) z = -deriv (deriv f) z / (deriv f z)^2 :=
    (han.deriv.differentiableAt.hasDerivAt.inv hd).deriv
  rw [logarithmicJet, hq, reciprocalDeriv]
  field_simp

def criticalMap (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  f z - Complex.I / (k : ℂ) * (z.im : ℂ) * deriv f z

def normalizedJacobian (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap / ‖deriv f z‖^2

lemma fderiv_criticalMap_apply {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (v : ℂ) :
    fderiv ℝ (criticalMap f k) z v = deriv f z * v -
      Complex.I / (k : ℂ) * ((v.im : ℂ) * deriv f z +
        (z.im : ℂ) * (deriv (deriv f) z * v)) := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have ha := han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hb := han.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hG := ha.sub ((hc.const_mul (Complex.I / (k : ℂ))).mul hb)
  have hG' : HasFDerivAt (criticalMap f k)
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) -
        ((Complex.I / (k : ℂ) * (z.im : ℂ)) •
          ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv f) z)) +
        deriv f z • (Complex.I / (k : ℂ)) •
          (Complex.ofRealCLM.comp Complex.imCLM))) z := hG
  rw [hG'.fderiv]
  change v * deriv f z -
    ((Complex.I / (k : ℂ) * (z.im : ℂ)) * (v * deriv (deriv f) z) +
      deriv f z * (Complex.I / (k : ℂ) * (v.im : ℂ))) = _
  ring

lemma criticalMap_columns {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    fderiv ℝ (criticalMap f k) z 1 = deriv f z / (k : ℂ) * ((k : ℂ) + logarithmicJet f z) ∧
    fderiv ℝ (criticalMap f k) z Complex.I =
      Complex.I * (deriv f z / (k : ℂ)) * ((k : ℂ) - 1 + logarithmicJet f z) := by
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  constructor <;> rw [fderiv_criticalMap_apply hf hz, logarithmicJet_eq hf hz] <;>
    simp only [Complex.one_im, Complex.I_im, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, one_mul, mul_one, zero_add] <;> field_simp <;> ring

lemma critical_columns_det (u q : ℂ) (k : ℝ) :
    (u * ((k : ℂ) + q)).re * (Complex.I * u * ((k : ℂ) - 1 + q)).im -
      (Complex.I * u * ((k : ℂ) - 1 + q)).re * (u * ((k : ℂ) + q)).im =
    ‖u‖^2 * (k * (k-1) + (2*k-1)*q.re + ‖q‖^2) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

lemma normalizedJacobian_formula {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    k^2 * normalizedJacobian f k z =
      k * (k - 1) + (2*k - 1) * (logarithmicJet f z).re + ‖logarithmicJet f z‖^2 := by
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  obtain ⟨hc₁, hc₂⟩ := criticalMap_columns hf hz k hk
  rw [normalizedJacobian, determinant_complex_real]
  change k ^ 2 * (((fderiv ℝ (criticalMap f k) z 1).re *
    (fderiv ℝ (criticalMap f k) z Complex.I).im -
    (fderiv ℝ (criticalMap f k) z Complex.I).re *
    (fderiv ℝ (criticalMap f k) z 1).im) / ‖deriv f z‖^2) = _
  rw [hc₁, hc₂, critical_columns_det, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

lemma hasDerivAt_reciprocalDeriv {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    HasDerivAt (reciprocalDeriv f) (deriv (reciprocalDeriv f) z) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact (han.deriv.differentiableAt.inv
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)).hasDerivAt

lemma logarithmicJet_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    logarithmicJet (reroot f z) w = logarithmicJet f (affine z w) := by
  have hqz : reciprocalDeriv f z ≠ 0 := inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  have hqw : reciprocalDeriv f (affine z w) ≠ 0 := inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane hf (affine_mem hz hw))
  have heq : reciprocalDeriv (reroot f z) =ᶠ[𝓝 w]
      (fun u => reciprocalDeriv f (affine z u) / reciprocalDeriv f z) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hw] with u hu
    exact reciprocalDeriv_reroot hf hz hu
  have hD := ((((hasDerivAt_reciprocalDeriv hf (affine_mem hz hw)).comp w
    (hasDerivAt_affine z w)).div_const (reciprocalDeriv f z)).congr_of_eventuallyEq heq).deriv
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  rw [logarithmicJet, hD, reciprocalDeriv_reroot hf hz hw, logarithmicJet, him]
  field_simp

lemma criticalMap_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (k : ℝ) :
    criticalMap (reroot f z) k w =
      (criticalMap f k (affine z w) - f z) / ((z.im : ℂ) * deriv f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  rw [criticalMap, deriv_reroot hf hz hw]
  simp only [reroot, criticalMap, him]
  field_simp
  ring

lemma normalizedJacobian_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    normalizedJacobian (reroot f z) k w = normalizedJacobian f k (affine z w) := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hk))
  rw [normalizedJacobian_formula (reroot_normalized hf hz).1 hw k hk,
    normalizedJacobian_formula hf (affine_mem hz hw) k hk, logarithmicJet_reroot hf hz hw]

def potential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal z.im) ^ k / ENNReal.ofReal ‖f z - ξ‖

def GoodPair (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Prop :=
  (∀ δ : ℝ, 0 < δ → IsCompact {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z}) ∧
  (∀ z ∈ halfPlane, criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0)

def CriticalCountStatement : Prop :=
  ∀ f : ℂ → ℂ, UnivalentOn f halfPlane → ∀ k : ℝ, 1 < k → ∀ ξ : ℂ,
    GoodPair f k ξ → ∀ h : ℝ, 0 < h →
      let critical := {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
        ENNReal.ofReal h ≤ potential f k ξ z}
      critical.Finite ∧
      ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
        ({z ∈ critical | normalizedJacobian f k z < 0}).ncard

lemma differentiableAt_criticalMap {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) :
    DifferentiableAt ℝ (criticalMap f k) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact ((han.differentiableAt.restrictScalars ℝ).sub
    (((Complex.ofRealCLM.differentiableAt.comp z Complex.imCLM.differentiableAt).const_mul
      (Complex.I / (k : ℂ))).mul (han.deriv.differentiableAt.restrictScalars ℝ)))

lemma critical_fiber_discrete {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ : ℂ} (hreg : ∀ z ∈ halfPlane,
      criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0) :
    IsDiscrete {z | z ∈ halfPlane ∧ criticalMap f k z = ξ} := by
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have hd : LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap ≠ 0 :=
    (div_ne_zero_iff.mp (hreg z hz.1 hz.2)).1
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ (criticalMap f k) z := by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hd) w
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ (criticalMap f k) z) := by
    rw [← he]
    exact ⟨_, e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [(differentiableAt_criticalMap hf hz.1 k).hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw h.2

lemma finite_critical_superlevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z}.Finite := by
  let P := {z | z ∈ halfPlane ∧ ENNReal.ofReal h ≤ potential f k ξ z}
  have hP : IsCompact P := hg.1 h hh
  have hc : ContinuousOn (criticalMap f k) P := by
    intro z hz
    exact (differentiableAt_criticalMap hf hz.1 k).continuousAt.continuousWithinAt
  have hclosed := hc.preimage_isClosed_of_isClosed hP.isClosed (isClosed_singleton (x := ξ))
  have hcompact : IsCompact (P ∩ (criticalMap f k) ⁻¹' {ξ}) :=
    hP.of_isClosed_subset hclosed inter_subset_left
  have hdiscrete := (critical_fiber_discrete hf hg.2).mono
    (show P ∩ (criticalMap f k) ⁻¹' {ξ} ⊆
      {z | z ∈ halfPlane ∧ criticalMap f k z = ξ} from fun _ hz => ⟨hz.1.1, hz.2⟩)
  convert hcompact.finite hdiscrete using 1
  ext z
  simp only [P, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
  tauto

def logPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  k * Real.log z.im - Real.log ‖f z - ξ‖

lemma differentiableAt_log_norm {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (hn : g z ≠ 0) :
    DifferentiableAt ℝ (fun w => Real.log ‖g w‖) z :=
  ((hg.restrictScalars ℝ).norm ℂ hn).log (norm_ne_zero_iff.mpr hn)

lemma fderiv_log_norm_apply {g : ℂ → ℂ} {d z : ℂ} (hg : HasDerivAt g d z)
    (hn : g z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => Real.log ‖g w‖) z v = (d * v / g z).re := by
  have heq : (fun w => Real.log ‖g w‖) =
      (fun w => (1 / 2 : ℝ) * Real.log (‖g w‖ ^ 2)) := by
    funext w
    rw [Real.log_pow]
    ring
  have hh := (((hg.hasFDerivAt.restrictScalars ℝ).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1 / 2 : ℝ)
  rw [heq, hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im, Complex.div_re, Complex.normSq_eq_norm_sq]
  ring

lemma differentiableAt_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    DifferentiableAt ℝ (logPotential f k ξ) z := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  exact ((Complex.imCLM.differentiableAt.log (ne_of_gt hz)).const_mul k).sub
    (differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp))

lemma fderiv_logPotential_apply {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    fderiv ℝ (logPotential f k ξ) z v =
      k / z.im * v.im - (deriv f z * v / (f z - ξ)).re := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have ha := (Complex.imCLM.hasFDerivAt.log (ne_of_gt hz)).const_mul k
  simp only [Complex.imCLM_apply] at ha
  have hb := differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp)
  change fderiv ℝ (fun w => k * Real.log w.im - Real.log ‖f w - ξ‖) z v = _
  rw [fderiv_fun_sub ha.differentiableAt hb,
    sub_apply, ha.fderiv,
    fderiv_log_norm_apply (hd.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)]
  simp only [smul_apply, smul_eq_mul, Complex.imCLM_apply, div_eq_mul_inv]
  ring

lemma criticalMap_ne_pole {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) : f z ≠ ξ := by
  intro hp
  have hn := mul_ne_zero (mul_ne_zero (div_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hk)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  apply hn
  simpa [criticalMap, hp] using hc

lemma critical_difference {f : ℂ → ℂ} {k : ℝ} {z ξ : ℂ}
    (hc : criticalMap f k z = ξ) :
    f z - ξ = Complex.I / (k : ℂ) * (z.im : ℂ) * deriv f z := by
  unfold criticalMap at hc
  linear_combination hc

lemma ratio_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    deriv f z / (f z - ξ) = -Complex.I * (k : ℂ) / (z.im : ℂ) := by
  have hd := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hy := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [critical_difference hc]
  field_simp
  simp [Complex.I_sq]

lemma criticalMap_eq_of_ratio {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ)
    (hr : deriv f z / (f z - ξ) = -Complex.I * (k : ℂ) / (z.im : ℂ)) :
    criticalMap f k z = ξ := by
  have hy := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hk' := Complex.ofReal_ne_zero.mpr hk
  have hdiff := sub_ne_zero.mpr hp
  have hd := (div_eq_iff hdiff).mp hr
  rw [criticalMap, hd]
  field_simp
  simp [Complex.I_sq]

lemma critical_iff_fderiv_logPotential_zero {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    criticalMap f k z = ξ ↔ fderiv ℝ (logPotential f k ξ) z = 0 := by
  constructor
  · intro hc
    ext v
    rw [fderiv_logPotential_apply hf hz hp]
    have hr := ratio_at_critical hf hz hc
    rw [show deriv f z * v / (f z - ξ) = (deriv f z / (f z - ξ)) * v by ring, hr]
    simp [Complex.div_re, Complex.div_im, Complex.normSq_ofReal]
    field_simp
    ring
  · intro heq
    have hx := congrArg (fun A : ℂ →L[ℝ] ℝ => A 1) heq
    have hy := congrArg (fun A : ℂ →L[ℝ] ℝ => A Complex.I) heq
    rw [fderiv_logPotential_apply hf hz hp] at hx hy
    simp only [Complex.one_im, mul_zero, mul_one, zero_apply,
      zero_sub, neg_eq_zero] at hx
    have him : (deriv f z / (f z - ξ)).im = -(k / z.im) := by
      rw [show deriv f z * Complex.I / (f z - ξ) =
        (deriv f z / (f z - ξ)) * Complex.I by ring] at hy
      simp only [Complex.I_im, mul_one, Complex.mul_I_re,
        zero_apply] at hy
      linarith
    apply criticalMap_eq_of_ratio hk hz hp
    apply Complex.ext
    · simpa using hx
    · simpa [neg_div] using him

def targetRatio (f : ℂ → ℂ) (ξ z : ℂ) : ℂ := deriv f z / (f z - ξ)

lemma hasDerivAt_targetRatio {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    HasDerivAt (targetRatio f ξ)
      ((deriv (deriv f) z * (f z - ξ) - deriv f z * deriv f z) / (f z - ξ)^2) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact han.deriv.differentiableAt.hasDerivAt.div
    (han.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)

lemma deriv_targetRatio_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    deriv (targetRatio f ξ) z = (k : ℂ) * (k + logarithmicJet f z) / (z.im : ℂ)^2 := by
  have hd := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hy := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hk' := Complex.ofReal_ne_zero.mpr hk
  rw [(hasDerivAt_targetRatio hf hz (criticalMap_ne_pole hf hk hz hc)).deriv,
    critical_difference hc, logarithmicJet_eq hf hz]
  field_simp
  simp only [Complex.I_sq]
  ring_nf

def secondDirectional (u : ℂ → ℝ) (z v w : ℂ) : ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t v) z w

def realHessian (u : ℂ → ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![secondDirectional u z 1 1, secondDirectional u z 1 Complex.I;
    secondDirectional u z Complex.I 1, secondDirectional u z Complex.I Complex.I]

lemma secondDirectional_logPotential_one {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z 1 v =
      -(deriv (targetRatio f ξ) z * v).re := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w 1) =ᶠ[𝓝 z]
      (fun w => -(targetRatio f ξ w).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    simp only [fderiv_logPotential_apply hf hw hne, Complex.one_im, mul_zero,
      mul_one, zero_sub, targetRatio]
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have hh := (Complex.reCLM.hasFDerivAt.comp z
    (hr.hasFDerivAt.restrictScalars ℝ)).neg
  change HasFDerivAt (fun w => -(targetRatio f ξ w).re) _ z at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Complex.reCLM_apply, mul_comm v]

lemma secondDirectional_logPotential_I {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z Complex.I v =
      -k / z.im^2 * v.im + (deriv (targetRatio f ξ) z * v).im := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w Complex.I) =ᶠ[𝓝 z]
      (fun w => k / w.im + (targetRatio f ξ w).im) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne,
      show deriv f w * Complex.I / (f w - ξ) =
        (deriv f w / (f w - ξ)) * Complex.I by ring]
    simp only [Complex.I_im, mul_one, Complex.mul_I_re, sub_neg_eq_add, targetRatio]
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have ha := (((hasDerivAt_inv (ne_of_gt hz)).hasFDerivAt).comp z
    Complex.imCLM.hasFDerivAt).const_mul k
  have hb := Complex.imCLM.hasFDerivAt.comp z (hr.hasFDerivAt.restrictScalars ℝ)
  have hh := ha.add hb
  change HasFDerivAt (fun w => k * w.im⁻¹ + (targetRatio f ξ w).im) _ z at hh
  simp only [← div_eq_mul_inv] at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply, mul_comm v]
  ring

lemma realHessian_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    realHessian (logPotential f k ξ) z =
      !![-(deriv (targetRatio f ξ) z).re, (deriv (targetRatio f ξ) z).im;
        (deriv (targetRatio f ξ) z).im, -k / z.im^2 + (deriv (targetRatio f ξ) z).re] := by
  simp only [realHessian, secondDirectional_logPotential_one hf hz hp,
    secondDirectional_logPotential_I hf hz hp, mul_one, Complex.mul_I_re,
    Complex.mul_I_im, Complex.one_im, Complex.I_im, mul_zero, mul_one, zero_add, neg_neg]

lemma trace_realHessian_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    Matrix.trace (realHessian (logPotential f k ξ) z) = -k / z.im^2 := by
  rw [realHessian_logPotential hf hz hp]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

lemma realHessian_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    realHessian (logPotential f k ξ) z =
      (k / z.im^2) •
        !![-(k + (logarithmicJet f z).re), (logarithmicJet f z).im;
          (logarithmicJet f z).im, k - 1 + (logarithmicJet f z).re] := by
  rw [realHessian_logPotential hf hz (criticalMap_ne_pole hf hk hz hc),
    deriv_targetRatio_at_critical hf hk hz hc]
  have hre : ((k : ℂ) * (k + logarithmicJet f z) / (z.im : ℂ)^2).re =
      k / z.im^2 * (k + (logarithmicJet f z).re) := by
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  have him : ((k : ℂ) * (k + logarithmicJet f z) / (z.im : ℂ)^2).im =
      k / z.im^2 * (logarithmicJet f z).im := by
    rw [← Complex.ofReal_pow, Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_add]
    ring
  rw [hre, him]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> ring

lemma det_realHessian_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    (realHessian (logPotential f k ξ) z).det =
      -(k^4 / z.im^4) * normalizedJacobian f k z := by
  rw [realHessian_at_critical hf hk hz hc, Matrix.det_fin_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hJ := normalizedJacobian_formula hf hz k hk
  rw [Complex.sq_norm, Complex.normSq_apply] at hJ
  have hy : z.im ≠ 0 := ne_of_gt hz
  field_simp
  linear_combination hJ

lemma trace_realHessian_negative {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    Matrix.trace (realHessian (logPotential f k ξ) z) < 0 := by
  rw [trace_realHessian_logPotential hf hz hp]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hk) (sq_pos_of_pos hz)

lemma det_realHessian_ne_zero_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ}
    (hz : z ∈ halfPlane) (hc : criticalMap f k z = ξ)
    (hJ : normalizedJacobian f k z ≠ 0) :
    (realHessian (logPotential f k ξ) z).det ≠ 0 := by
  rw [det_realHessian_at_critical hf hk hz hc]
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 4 hk)
    (pow_ne_zero 4 (ne_of_gt hz)))) hJ

lemma potential_off_pole {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    potential f k ξ z = ENNReal.ofReal (z.im^k / ‖f z - ξ‖) := by
  rw [potential, ENNReal.ofReal_rpow_of_pos hz,
    ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))]

lemma potential_pos {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane) :
    0 < potential f k ξ z := by
  rw [potential]
  exact ENNReal.div_pos (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hz)
    ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top

lemma potential_at_pole {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z = ξ) : potential f k ξ z = ∞ := by
  rw [potential, hp, sub_self, norm_zero, ENNReal.ofReal_zero]
  exact ENNReal.div_zero (ne_of_gt (ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr hz) ENNReal.ofReal_ne_top))

lemma potential_critical_height {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    potential f k ξ z = ENNReal.ofReal (k * z.im^(k-1) * ‖reciprocalDeriv f z‖) := by
  have hd := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hn : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [potential_off_pole hz (criticalMap_ne_pole hf (ne_of_gt hk) hz hc),
    critical_difference hc, norm_mul, norm_mul, norm_div, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hk, abs_of_pos hz, Real.rpow_sub_one hy, reciprocalDeriv, norm_inv]
  congr 1
  field_simp

lemma critical_target_weight {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {β : ℝ} (hβ : 1 < β) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f ((β+3)/4) z = ξ) :
    z.im^(β-1) * ‖reciprocalDeriv f z‖^4 =
      ((potential f ((β+3)/4) ξ z).toReal / ((β+3)/4))^4 := by
  let k : ℝ := (β+3)/4
  have hk : 0 < k := by dsimp [k]; linarith
  have hv : 0 ≤ k * z.im^(k-1) * ‖reciprocalDeriv f z‖ :=
    mul_nonneg (mul_nonneg hk.le (Real.rpow_nonneg hz.le _)) (norm_nonneg _)
  rw [potential_critical_height hf hk hz hc, ENNReal.toReal_ofReal hv]
  have he : β - 1 = (k - 1) * 4 := by dsimp [k]; ring
  rw [he, Real.rpow_mul (le_of_lt hz)]
  change (z.im ^ (k - 1)) ^ (4 : ℝ) * _ = (k * _ * _ / k) ^ (4 : ℕ)
  rw [Real.rpow_ofNat]
  field_simp

end Brennan

end

end OAI
