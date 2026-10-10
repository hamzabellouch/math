import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def HasWeakDirectionalDerivative (f g : V → ℂ) (v : V) : Prop :=
  ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, g x * (φ x : ℂ))

def testBump : ContDiffBump (0 : V) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def testScale (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

def testCutoff (n : ℕ) (x : V) : ℝ := (testBump (V := V)) (testScale n • x)

lemma testScale_pos (n : ℕ) : 0 < testScale n := by unfold testScale; positivity
lemma testScale_le_one (n : ℕ) : testScale n ≤ 1 := by
  unfold testScale
  exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
lemma testScale_tendsto : Tendsto testScale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
    (fun n : ℕ => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1) tendsto_natCast_atTop_atTop)

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (testCutoff (V := V) n) :=
  (testBump (V := V)).contDiff.comp (contDiff_id.const_smul _)

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_compact (n : ℕ) : HasCompactSupport (testCutoff (V := V) n) :=
  (testBump (V := V)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (testScale n) (testScale_pos n).ne')

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_norm_le (n : ℕ) (x : V) : ‖testCutoff n x‖ ≤ 1 := by
  change ‖(testBump (V := V)) (testScale n • x)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (testBump (V := V)).nonneg]
  exact (testBump (V := V)).le_one

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_tendsto (x : V) : Tendsto (fun n => testCutoff n x) atTop (𝓝 1) := by
  have hh := (testBump (V := V)).continuous.continuousAt.tendsto.comp (testScale_tendsto.smul_const x)
  have hz : (testBump (V := V)) 0 = 1 :=
    (testBump (V := V)).one_of_mem_closedBall (by simp [testBump])
  simpa only [zero_smul, hz, testCutoff, Function.comp_def] using hh

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_derivative (n : ℕ) (x v : V) :
    fderiv ℝ (testCutoff n) x v =
      testScale n * fderiv ℝ (testBump (V := V) : V → ℝ) (testScale n • x) v := by
  have hh := ((((testBump (V := V)).contDiff (n := ⊤)).differentiable (by simp) (testScale n • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (testScale n))
  have he := congrArg (fun L : V →L[ℝ] ℝ => L v) hh.fderiv
  refine he.trans ?_
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul]

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_derivative_control (v : V) : ∃ D : ℝ, 0 ≤ D ∧
    (∀ n x, ‖fderiv ℝ (testCutoff n) x v‖ ≤ D) ∧
    (∀ x, Tendsto (fun n => fderiv ℝ (testCutoff n) x v) atTop (𝓝 0)) := by
  obtain ⟨C, hC⟩ := (((testBump (V := V)).contDiff (n := ⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((testBump (V := V)).hasCompactSupport.fderiv ℝ)
  let D := max C 0 * ‖v‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (n : ℕ) (x : V) : ‖fderiv ℝ (testCutoff n) x v‖ ≤ testScale n * D := by
    rw [testCutoff_derivative, norm_mul, Real.norm_eq_abs, abs_of_pos (testScale_pos n)]
    apply mul_le_mul_of_nonneg_left _ (testScale_pos n).le
    exact ((fderiv ℝ (testBump (V := V) : V → ℝ) (testScale n • x)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hC _).trans (le_max_left _ _)) (norm_nonneg v))
  refine ⟨D, hD, fun n x => (hb n x).trans ?_, fun x => ?_⟩
  · exact (mul_le_mul_of_nonneg_right (testScale_le_one n) hD).trans_eq (one_mul D)
  · exact squeeze_zero_norm (fun n => hb n x) (by simpa using testScale_tendsto.mul_const D)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma fderiv_mul_real {φ χ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (x v : V) :
    fderiv ℝ (fun y => χ y * φ y) x v = fderiv ℝ χ x v * φ x + χ x * fderiv ℝ φ x v := by
  have hd := ((hχ.differentiable (by simp) x).hasFDerivAt).mul
    ((hφ.differentiable (by simp) x).hasFDerivAt)
  have he := congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv
  refine he.trans ?_
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma weak_derivative_smooth_L2 {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφL : MemLp φ 2)
    (hφD : MemLp (fun x => fderiv ℝ φ x v) 2) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)) := by
  obtain ⟨D, hD, hbound, htendsto⟩ := testCutoff_derivative_control v
  let φn : ℕ → V → ℝ := fun n x => testCutoff n x * φ x
  have hs (n : ℕ) : ContDiff ℝ ∞ (φn n) := (testCutoff_smooth n).mul hφ
  have hcompact (n : ℕ) : HasCompactSupport (φn n) := (testCutoff_compact n).mul_right
  have hd (n : ℕ) (x : V) : fderiv ℝ (φn n) x v =
      fderiv ℝ (testCutoff n) x v * φ x + testCutoff n x * fderiv ℝ φ x v :=
    fderiv_mul_real hφ (testCutoff_smooth n) x v
  have hi1 := hf.norm.integrable_mul hφL.norm
  have hi2 := hf.norm.integrable_mul hφD.norm
  have ha : Tendsto (fun n => ∫ x, f x * (fderiv ℝ (φn n) x v : ℂ)) atTop
      (𝓝 (∫ x, f x * (fderiv ℝ φ x v : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => D * (‖f x‖ * ‖φ x‖) + ‖f x‖ * ‖fderiv ℝ φ x v‖)
    · exact Eventually.of_forall (fun n => hf.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (((hs n).continuous_fderiv (by simp)).clm_apply
          continuous_const)).aestronglyMeasurable))
    · refine Eventually.of_forall (fun n => Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, hd]
      calc
        _ ≤ ‖f x‖ * (‖fderiv ℝ (testCutoff n) x v‖ * ‖φ x‖ +
            ‖testCutoff n x‖ * ‖fderiv ℝ φ x v‖) := by
          gcongr; exact (norm_add_le _ _).trans_eq (by simp only [norm_mul])
        _ ≤ ‖f x‖ * (D * ‖φ x‖ + 1 * ‖fderiv ℝ φ x v‖) := by
          gcongr; exact hbound n x; exact testCutoff_norm_le n x
        _ = _ := by ring
    · exact (hi1.const_mul D).add hi2
    · refine Eventually.of_forall (fun x => ?_)
      simp_rw [hd]
      simpa only [zero_mul, one_mul, zero_add] using
        (((htendsto x).mul_const (φ x)).add
          ((testCutoff_tendsto x).mul_const (fderiv ℝ φ x v))).ofReal.const_mul (f x)
  have hb : Tendsto (fun n => ∫ x, g x * (φn n x : ℂ)) atTop
      (𝓝 (∫ x, g x * (φ x : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖ * ‖φ x‖)
    · exact Eventually.of_forall (fun n => hg.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (hs n).continuous).aestronglyMeasurable))
    · refine Eventually.of_forall (fun n => Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_real, φn]
      calc
        _ ≤ ‖g x‖ * (1 * ‖φ x‖) := by gcongr; exact testCutoff_norm_le n x
        _ = _ := by ring
    · exact hg.norm.integrable_mul hφL.norm
    · refine Eventually.of_forall (fun x => ?_)
      simpa only [one_mul, φn] using
        ((testCutoff_tendsto x).mul_const (φ x)).ofReal.const_mul (g x)
  apply tendsto_nhds_unique ha
  convert hb.neg using 1
  ext n
  have hh := hw (φn n) (hs n) (hcompact n)
  simpa only [((hs n).differentiable (by simp) _).lineDeriv_eq_fderiv] using hh

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma fderiv_schwartz_postcomp (φ : 𝓢(V, ℂ)) (L : ℂ →L[ℝ] ℝ) (x v : V) :
    fderiv ℝ (φ.postcompCLM L) x v = L (fderiv ℝ φ x v) := by
  have hh := L.hasFDerivAt.comp x (φ.differentiable x).hasFDerivAt
  exact congrArg (fun A : V →L[ℝ] ℝ => A v) hh.fderiv

lemma weak_derivative_schwartz {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v)
    (φ : 𝓢(V, ℂ)) :
    (∫ x, f x * fderiv ℝ φ x v) = -(∫ x, g x * φ x) := by
  let r : 𝓢(V, ℝ) := φ.postcompCLM Complex.reCLM
  let j : 𝓢(V, ℝ) := φ.postcompCLM Complex.imCLM
  let dr : 𝓢(V, ℝ) := SchwartzMap.evalCLM ℝ V ℝ v (SchwartzMap.fderivCLM ℝ V ℝ r)
  let dj : 𝓢(V, ℝ) := SchwartzMap.evalCLM ℝ V ℝ v (SchwartzMap.fderivCLM ℝ V ℝ j)
  have hdr : MemLp (fun x => fderiv ℝ (r : V → ℝ) x v) 2 volume := by
    convert dr.memLp 2 volume using 1
    ext x
    simp [dr, SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  have hdj : MemLp (fun x => fderiv ℝ (j : V → ℝ) x v) 2 volume := by
    convert dj.memLp 2 volume using 1
    ext x
    simp [dj, SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  have hr := weak_derivative_smooth_L2 hf hg hw (φ := (r : V → ℝ)) r.smooth' (r.memLp 2 volume) hdr
  have hj := weak_derivative_smooth_L2 hf hg hw (φ := (j : V → ℝ)) j.smooth' (j.memLp 2 volume) hdj
  have hcast (a : 𝓢(V, ℝ)) : MemLp (fun x => (a x : ℂ)) 2 volume := by
    convert (a.postcompCLM Complex.ofRealCLM).memLp 2 volume using 1
    ext x
    simp
  have hdecomp (x : V) : fderiv ℝ φ x v = (dr x : ℂ) + (dj x : ℂ) * Complex.I := by
    change fderiv ℝ φ x v = (fderiv ℝ r x v : ℂ) + (fderiv ℝ j x v : ℂ) * Complex.I
    rw [fderiv_schwartz_postcomp, fderiv_schwartz_postcomp]
    exact (Complex.re_add_im _).symm
  have hdecomp' (x : V) : φ x = (r x : ℂ) + (j x : ℂ) * Complex.I :=
    (Complex.re_add_im _).symm
  have hir : Integrable (fun x => f x * (dr x : ℂ)) :=
    hf.integrable_mul (hcast dr)
  have hij : Integrable (fun x => f x * (dj x : ℂ)) :=
    hf.integrable_mul (hcast dj)
  have hgr : Integrable (fun x => g x * (r x : ℂ)) :=
    hg.integrable_mul (hcast r)
  have hgj : Integrable (fun x => g x * (j x : ℂ)) :=
    hg.integrable_mul (hcast j)
  calc
    _ = (∫ x, f x * (dr x : ℂ)) + (∫ x, f x * (dj x : ℂ)) * Complex.I := by
      simp_rw [hdecomp, mul_add, ← mul_assoc]
      rw [integral_add hir (hij.mul_const _), integral_mul_const]
    _ = -((∫ x, g x * (r x : ℂ)) + (∫ x, g x * (j x : ℂ)) * Complex.I) := by
      change (∫ x, f x * (fderiv ℝ r x v : ℂ)) +
        (∫ x, f x * (fderiv ℝ j x v : ℂ)) * Complex.I = _
      rw [hr, hj]
      ring
    _ = _ := by
      congr 1
      simp_rw [hdecomp', mul_add, ← mul_assoc]
      rw [integral_add hgr (hgj.mul_const _), integral_mul_const]

open LineDeriv in
lemma weak_derivative_tempered {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    ∂_{v} (Lp.toTemperedDistribution (hf.toLp f)) =
      Lp.toTemperedDistribution (hg.toLp g) := by
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [Lp.toTemperedDistribution_apply, neg_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, neg_mul, integral_neg]
  have h1 : (∫ x : V, fderiv ℝ φ x v * hf.toLp f x) =
      ∫ x : V, f x * fderiv ℝ φ x v := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have h2 : (∫ x : V, φ x * hg.toLp g x) = ∫ x : V, g x * φ x := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  rw [h1, h2, weak_derivative_schwartz hf hg hw φ, neg_neg]

open LineDeriv in
lemma weak_fourier_derivative_ae {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    (fun ξ => (𝓕 (hg.toLp g) : Lp ℂ 2 volume) ξ) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ) *
        (𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ) := by
  let F : Lp ℂ 2 (volume : Measure V) := 𝓕 (hf.toLp f)
  let G : Lp ℂ 2 (volume : Measure V) := 𝓕 (hg.toLp g)
  have hd := congrArg (fun d : 𝓢'(V, ℂ) => 𝓕 d) (weak_derivative_tempered hf hg hw)
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at hd
  have ht : (fun ξ : V => (inner ℝ ξ v : ℂ)).HasTemperateGrowth := by fun_prop
  have hc : Continuous (fun ξ : V => (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ)) := by
    fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp G |>.locallyIntegrable (by norm_num))
    (LocallyIntegrable.continuous_mul hc (Lp.memLp F |>.locallyIntegrable (by norm_num)))
  intro φ hφ hcompact
  let ψ : 𝓢(V, ℂ) := (hcompact.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hh := congrArg (fun d : 𝓢'(V, ℂ) => d ψ) hd
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    smul_eq_mul] at hh
  change (2 * Real.pi * Complex.I) *
      (∫ x, ((inner ℝ x v : ℂ) * ψ x) * F x) = ∫ x, ψ x * G x at hh
  simp only [Complex.real_smul]
  change (∫ x, ψ x * G x) = ∫ x, ψ x * ((2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ) * F x)
  rw [← hh, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    ring

lemma l2_norm_sq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ x, (‖u x‖ : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

lemma weak_fourier_moment {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    Integrable (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ, (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) = ∫ x, ‖g x‖^2 := by
  let G : Lp ℂ 2 (volume : Measure V) := 𝓕 (hg.toLp g)
  have hae : (fun ξ => ‖G ξ‖^2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) := by
    filter_upwards [weak_fourier_derivative_ae hf hg hw] with ξ hξ
    change ‖(𝓕 (hg.toLp g) : Lp ℂ 2 volume) ξ‖^2 = _
    rw [hξ]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      mul_one, mul_pow, Real.norm_eq_abs, sq_abs]
  have hi : Integrable (fun ξ => ‖G ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  refine ⟨hi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← l2_norm_sq_integral, Lp.norm_fourier_eq,
    l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

lemma weak_fourier_kinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f : V → ℂ} {g : ι → V → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i, HasWeakDirectionalDerivative f (g i) (b i)) :
    Integrable (fun ξ => (2 * Real.pi)^2 * ‖ξ‖^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ, (2 * Real.pi)^2 * ‖ξ‖^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) = ∑ i, ∫ x, ‖g i x‖^2 := by
  classical
  have he (ξ : V) : (2 * Real.pi)^2 * ‖ξ‖^2 *
      ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2 =
      ∑ i, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2 := by
    rw [← b.sum_sq_inner_left ξ, Finset.mul_sum, Finset.sum_mul]
  simp_rw [he]
  have hi (i : ι) := (weak_fourier_moment hf (hg i) (hw i)).1
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => (weak_fourier_moment hf (hg i) (hw i)).2)

lemma classical_fourier_continuous {f : V → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

lemma integral_fourier_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, (𝓕 f) ξ * g ξ) = ∫ x, f x * (𝓕 g) x := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ V) Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf hg
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    exact real_inner_comm x y
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) f ξ * g ξ) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) g x
  simpa only [smul_eq_mul, hflip] using he

lemma l2_fourier_ae_classical {f : V → ℂ} (hf : MemLp f 2) (hfi : Integrable f) :
    (fun ξ => (𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ) =ᵐ[volume] (𝓕 f) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp (𝓕 (hf.toLp f)) |>.locallyIntegrable (by norm_num))
    (classical_fourier_continuous hfi |>.locallyIntegrable)
  intro φ hφ hcompact
  let ψ : 𝓢(V, ℂ) := (hcompact.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hd := congrArg (fun d : 𝓢'(V, ℂ) => d ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  simp only [Complex.real_smul]
  change (∫ ξ, ψ ξ * (𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ) = ∫ ξ, ψ ξ * (𝓕 f) ξ
  rw [← hd]
  calc
    _ = ∫ x, (𝓕 (ψ : V → ℂ)) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      rfl
    _ = _ := integral_fourier_mul ψ.integrable hfi

lemma integrable_mul_real_test {f : V → ℂ} (hf : MemLp f 2)
    {φ : V → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => f x * (φ x : ℂ)) := by
  simpa only [Complex.real_smul, mul_comm] using
    (hf.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)).integrable_smul_left_of_hasCompactSupport hφ hcφ

lemma weak_derivative_mul_cutoff {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) :
    HasWeakDirectionalDerivative (fun x => f x * (η x : ℂ))
      (fun x => g x * (η x : ℂ) + f x * Complex.ofReal (lineDeriv ℝ η x v)) v := by
  intro φ hφ hcφ
  have hDη : Continuous (fun x => lineDeriv ℝ η x v) := by
    simp_rw [(hη.differentiable (by simp) _).lineDeriv_eq_fderiv]
    exact (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφ : Continuous (fun x => lineDeriv ℝ φ x v) := by
    simp_rw [(hφ.differentiable (by simp) _).lineDeriv_eq_fderiv]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcDφ : HasCompactSupport (fun x => lineDeriv ℝ φ x v) := by
    simp_rw [(hφ.differentiable (by simp) _).lineDeriv_eq_fderiv]
    exact (hcφ.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℝ => L v) (by rfl)
  have hd (x : V) : lineDeriv ℝ (fun y => η y * φ y) x v =
      lineDeriv ℝ η x v * φ x + η x * lineDeriv ℝ φ x v := by
    simp only [((hη.mul hφ).differentiable (by simp) x).lineDeriv_eq_fderiv,
      (hη.differentiable (by simp) x).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    change fderiv ℝ (η * φ) x v = _
    rw [(((hη.differentiable (by simp) x).hasFDerivAt).mul
      ((hφ.differentiable (by simp) x).hasFDerivAt)).fderiv]
    simp; ring
  have hA := integrable_mul_real_test hf (hη.continuous.mul hDφ) hcDφ.mul_left
  have hB := integrable_mul_real_test hf (hDη.mul hφ.continuous) hcφ.mul_left
  have hC := integrable_mul_real_test hg (hη.continuous.mul hφ.continuous) hcφ.mul_left
  have hA' : Integrable (fun x => (f x * (η x : ℂ)) * Complex.ofReal (lineDeriv ℝ φ x v)) := by
    simpa only [Pi.mul_apply, Complex.ofReal_mul, mul_assoc] using hA
  have hB' : Integrable (fun x => (f x * Complex.ofReal (lineDeriv ℝ η x v)) * (φ x : ℂ)) := by
    simpa only [Pi.mul_apply, Complex.ofReal_mul, mul_assoc] using hB
  have hC' : Integrable (fun x => (g x * (η x : ℂ)) * (φ x : ℂ)) := by
    simpa only [Pi.mul_apply, Complex.ofReal_mul, mul_assoc] using hC
  have h := hw (fun y => η y * φ y) (hη.mul hφ) hcφ.mul_left
  simp only [hd, Complex.ofReal_add, Complex.ofReal_mul, mul_add, ← mul_assoc] at h
  rw [integral_add hB' hA'] at h
  simp only [add_mul]
  rw [integral_add hC' hB']
  linear_combination h

open scoped LineDeriv

lemma complex_schwartz_shift_memLp (g : 𝓢(V, ℝ)) (z : V) (p : ℝ≥0∞) :
    MemLp (fun x : V => (g (x-z) : ℂ)) p := by
  have hg := (g.compSubConstCLM ℝ z).memLp p (volume : Measure V)
  exact hg.ofReal

lemma weak_window_memLp {f : V → ℂ} (hf : MemLp f 2) (g : 𝓢(V, ℝ)) (z : V) :
    MemLp (fun x => f x * (g (x-z) : ℂ)) 2 :=
  by simpa only [mul_comm] using hf.fun_mul (complex_schwartz_shift_memLp g z ∞)

lemma weak_window_integrable {f : V → ℂ} (hf : MemLp f 2) (g : 𝓢(V, ℝ)) (z : V) :
    Integrable (fun x => f x * (g (x-z) : ℂ)) :=
  hf.integrable_mul (complex_schwartz_shift_memLp g z 2)

lemma weak_window_derivative {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    {v : V} (hw : HasWeakDirectionalDerivative f u v) (g : 𝓢(V, ℝ)) (z : V) :
    HasWeakDirectionalDerivative (fun x => f x * (g (x-z) : ℂ))
      (fun x => u x * (g (x-z) : ℂ) + f x * (∂_{v} g (x-z) : ℂ)) v := by
  have hη : ContDiff ℝ ∞ (fun x : V => g (x-z)) :=
    g.smooth'.comp (contDiff_id.sub contDiff_const)
  have hd (x : V) : lineDeriv ℝ (fun y => g (y-z)) x v = ∂_{v} g (x-z) := by
    rw [(hη.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simpa only [Function.comp_def, id_eq, SchwartzMap.lineDerivOp_apply_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun L : V →L[ℝ] ℝ => L v)
        ((g.differentiable (x-z)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).sub_const z)).fderiv
  simpa only [hd] using weak_derivative_mul_cutoff hf hu hw hη

end CoulombAtom

end

end OAI
