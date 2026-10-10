import OAI.Analysis.DiskMaximal.BandBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Directional, coordinate-free distributional gradient. -/
def HasGradient (f : E → ℝ) (g : E → E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ v : E,
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -∫ x, ⟪g x,v⟫ * φ x ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma HasGradient.congr_ae {f f' : E → ℝ} {g g' : E → E}
    (h : HasGradient (μ := μ) f g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    HasGradient (μ := μ) f' g' := by
  intro φ hφ hc v
  calc
    _ = (∫ x, f x * fderiv ℝ φ x v ∂μ) := integral_congr_ae (hf.symm.mono (fun _ hx => by simp only [hx]))
    _ = _ := h φ hφ hc v
    _ = _ := by congr 1; exact integral_congr_ae (hg.mono (fun _ hx => by simp only [hx]))

lemma contDiff_hasGradient {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  simp_rw [inner_gradient_left]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro x _; exact hf.differentiable one_ne_zero x
  · intro x _; exact hφ.differentiable (by simp) x

omit [μ.IsAddHaarMeasure] in
lemma HasGradient.mul_contDiff {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    HasGradient (μ := μ) (fun x => χ x*f x)
      (fun x => χ x • g x + f x • gradient χ x) := by
  intro φ hφ hφc v
  have hdχ : Continuous (fun x => fderiv ℝ χ x v) := (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun x => f x*(χ x*fderiv ℝ φ x v)) μ :=
    hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hdφ) hc.mul_right
  have h2 : Integrable (fun x => f x*(φ x*fderiv ℝ χ x v)) μ :=
    hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hφ.continuous.mul hdχ) hφc.mul_right
  have h3 : Integrable (fun x => ⟪g x,v⟫*(χ x*φ x)) μ :=
    (hg.inner_const (𝕜 := ℝ) v).locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hφ.continuous) hc.mul_right
  have h := hw (χ*φ) (hχ.mul hφ) (hc.mul_right) v
  have he (x) : fderiv ℝ (χ*φ) x v = χ x*fderiv ℝ φ x v+φ x*fderiv ℝ χ x v := by
    rw [fderiv_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    rfl
  simp_rw [he,mul_add] at h
  rw [integral_add h1 h2] at h
  have he2 (x) : ⟪χ x • g x + f x • gradient χ x,v⟫ * φ x =
      ⟪g x,v⟫*(χ x*φ x)+f x*(φ x*fderiv ℝ χ x v) := by
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left]
    ring
  simp_rw [he2]
  rw [integral_add h3 h2]
  have hi : (∫ x, χ x*f x*fderiv ℝ φ x v ∂μ) = ∫ x, f x*(χ x*fderiv ℝ φ x v) ∂μ := by
    congr 1; ext x; ring
  rw [hi]
  simp only [Pi.mul_apply] at h
  linarith

lemma gradient_convolution {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (x : E) :
    gradient (f ⋆[lsmul ℝ ℝ,μ] K) x = (K ⋆[lsmul ℝ ℝ,μ] g) x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable (hK.of_le (by simp)) x).fderiv]
  rw [convolution_precompR_apply _ hf.locallyIntegrable (hc.fderiv ℝ) (hK.continuous_fderiv (by simp))]
  let ψ : E → ℝ := fun y => K (x-y)
  have hψ : ContDiff ℝ ∞ ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y) : fderiv ℝ ψ y v = -(fderiv ℝ K (x-y) v) := by
    have he := (hK.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change fderiv ℝ (K ∘ (fun y => x-y)) y v = _
    rw [he.fderiv]
    simp
  have he := hw ψ hψ hcψ v
  simp_rw [hd,mul_neg] at he
  rw [integral_neg,neg_inj] at he
  have hi := (hc.convolutionExists_left (lsmul ℝ ℝ) hK.continuous hg.locallyIntegrable x).integrable_swap
  change Integrable (fun y => K (x-y) • g y) μ at hi
  calc
    _ = ∫ y, ⟪g y,v⟫ * K (x-y) ∂μ := he
    _ = ⟪∫ y, K (x-y) • g y ∂μ,v⟫ := by
      rw [real_inner_comm,← integral_inner (𝕜 := ℝ) hi]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [real_inner_smul_right,real_inner_comm]; ring)
    _ = _ := by rw [convolution_eq_swap]; rfl

lemma norm_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : E → ℝ} {g : E → F}
    (hK : Integrable K μ) (hg : Integrable g μ) :
    (∫ x, ‖(K ⋆[lsmul ℝ ℝ,μ] g) x‖ ∂μ) ≤ (∫ x, |K x| ∂μ)*(∫ x, ‖g x‖ ∂μ) := by
  have hi := hK.norm.integrable_convolution (lsmul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x, ( (fun y => ‖K y‖) ⋆[lsmul ℝ ℝ,μ] (fun y => ‖g y‖)) x ∂μ := by
      apply integral_mono_ae (hK.integrable_convolution (lsmul ℝ ℝ) hg).norm hi
      filter_upwards [hK.norm.ae_convolution_exists (lsmul ℝ ℝ) hg.norm] with x hx
      simp only [convolution_def,lsmul_apply,smul_eq_mul] at hx ⊢
      exact norm_integral_le_of_norm_le hx (ae_of_all _ (fun y => by rw [norm_smul]))
    _ = _ := by rw [integral_convolution _ hK.norm hg.norm]; simp only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs]

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution

/-- Scheffe's argument for vector-valued L1 functions, without an a priori
pointwise dominating function for the approximating sequence. -/
lemma norm_sub_tendsto_zero {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {u : ℕ → α → F}
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖u n x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ) :
    Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0) := by
  let d := fun n x => ‖u n x‖+‖f x‖-‖u n x-f x‖
  have hd0 (n x) : 0 ≤ d n x := sub_nonneg.mpr (norm_sub_le _ _)
  have hd2 (n x) : d n x ≤ 2*‖f x‖ := by
    have hn := norm_le_norm_sub_add (u n x) (f x)
    dsimp [d]; linarith
  have hdint (n) : Integrable (d n) μ := ((hu n).norm.add hf.norm).sub ((hu n).sub hf).norm
  have hdt : Tendsto (fun n => ∫ x, d n x ∂μ) atTop (𝓝 (2*∫ x, ‖f x‖ ∂μ)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_of_dominated_convergence (fun x => 2*‖f x‖)
    · intro n; exact (hdint n).aestronglyMeasurable
    · exact hf.norm.const_mul 2
    · intro n; exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hd0 n x)]; exact hd2 n x)
    · filter_upwards [hlim] with x hx
      have he := (hx.norm.add (tendsto_const_nhds (x := ‖f x‖))).sub ((hx.sub (tendsto_const_nhds (x := f x))).norm)
      simpa only [sub_self,norm_zero,sub_zero,two_mul,d] using he
  have hle (n) : (∫ x, ‖u n x-f x‖ ∂μ) ≤ 2*(∫ x, ‖f x‖ ∂μ)-(∫ x, d n x ∂μ) := by
    have he : (∫ x, d n x ∂μ) = (∫ x, ‖u n x‖ ∂μ)+(∫ x, ‖f x‖ ∂μ)-(∫ x, ‖u n x-f x‖ ∂μ) := by
      exact (integral_sub ((hu n).norm.add hf.norm) ((hu n).sub hf).norm).trans (by simp only [Pi.add_apply, Pi.sub_apply]; rw [integral_add (hu n).norm hf.norm])
    rw [he]
    linarith [hbound n]
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hle
  simpa only [sub_self] using (tendsto_const_nhds (x := 2*∫ x, ‖f x‖ ∂μ)).sub hdt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A concrete normalized smooth approximate identity; all integrals retain the
ambient Haar measure, rather than changing normalization. -/
def mollifier (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1/((n:ℝ)+1)
  rOut := 2/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier (E := E) n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [mollifier,← mul_div_assoc,mul_one,mul_zero] using h

def smooth (f : E → ℝ) (n : ℕ) : E → ℝ := (mollifier n).normed μ ⋆[lsmul ℝ ℝ,μ] f

def smoothVector {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n : ℕ) : E → F :=
  (mollifier n).normed μ ⋆[lsmul ℝ ℝ,μ] f

lemma smoothVector_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : Integrable (smoothVector (μ := μ) f n) μ :=
  (mollifier n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf

lemma smoothVector_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : ContDiff ℝ ∞ (smoothVector (μ := μ) f n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (mollifier n).contDiff_normed hf.locallyIntegrable

lemma smoothVector_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) :
    (∫ x, ‖smoothVector (μ := μ) f n x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
  have h := norm_convolution_le (mollifier n).integrable_normed hf
  simpa only [smoothVector,abs_of_nonneg ((mollifier n).nonneg_normed (μ := μ) _),(mollifier n).integral_normed,mul_one,one_mul] using h

lemma smoothVector_converges {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖smoothVector (μ := μ) f n x-f x‖ ∂μ) atTop (𝓝 0) := by
  apply norm_sub_tendsto_zero hf (smoothVector_integrable hf)
  · exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable mollifier_radius_tendsto
      (Eventually.of_forall (fun n => (by dsimp [mollifier]; ring_nf; rfl : (mollifier (E := E) n).rOut ≤ 2*(mollifier n).rIn))) hf.locallyIntegrable
  · exact smoothVector_norm_le hf

lemma smooth_gradient {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) (n : ℕ) :
    gradient (smooth (μ := μ) f n) = smoothVector (μ := μ) g n := by
  ext x
  have h := gradient_convolution hf hg hw ((mollifier n).contDiff_normed (μ := μ)) ((mollifier n).hasCompactSupport_normed (μ := μ)) x
  have he : f ⋆[lsmul ℝ ℝ,μ] (mollifier n).normed μ = (mollifier n).normed μ ⋆[lsmul ℝ ℝ,μ] f := by
    ext z
    rw [convolution_def, convolution_def]
    simp only [lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self (fun y => f y * (mollifier n).normed μ (z-y)) μ z]
    simp only [sub_sub_cancel]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => mul_comm _ _)
  simpa only [smooth,smoothVector,he] using h

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def cutoff (n : ℕ) (x : E) : ℝ := (mollifier (E := E) 0) (((n:ℝ)+1)⁻¹ • x)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff (E := E) n) :=
  (mollifier 0).contDiff.comp (contDiff_const.smul contDiff_id)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (E := E) n) :=
  (mollifier 0).hasCompactSupport.comp_smul (by positivity)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_bound (n : ℕ) (x : E) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨(mollifier 0).nonneg, (mollifier 0).le_one⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ • x) atTop (𝓝 0) := by
    simpa only [one_div,zero_smul] using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x)
  have h := ((mollifier (E := E) 0).continuous.tendsto 0).comp ht
  have he : (mollifier (E := E) 0) (0:E) = 1 := (mollifier 0).one_of_mem_closedBall (mem_closedBall_self (mollifier 0).rIn_pos.le)
  rw [he] at h
  convert h using 1
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_gradient_fderiv (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_gradient_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ n x,
    ‖gradient (cutoff (E := E) n) x‖ ≤ L/((n:ℝ)+1) := by
  obtain ⟨L,hL⟩ := ((mollifier (E := E) 0).contDiff (n := (1:ℕ∞))).lipschitzWith_of_hasCompactSupport
    (mollifier 0).hasCompactSupport one_ne_zero
  refine ⟨L,L.coe_nonneg,?_⟩
  intro n x
  have he : LipschitzWith (L*‖((n:ℝ)+1)⁻¹‖₊) (cutoff (E := E) n) :=
    hL.comp (show LipschitzWith ‖((n:ℝ)+1)⁻¹‖₊ (fun x : E => ((n:ℝ)+1)⁻¹ • x) from
      lipschitzWith_smul (((n:ℝ)+1)⁻¹))
  rw [norm_gradient_fderiv]
  have hb := norm_fderiv_le_of_lipschitz ℝ he (x₀ := x)
  simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((n:ℝ)+1)⁻¹), div_eq_mul_inv] using hb

omit [μ.IsAddHaarMeasure] in
lemma cutoff_smul_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : Integrable (fun x => cutoff n x • f x) μ := by
  apply hf.bdd_smul 1 (cutoff_contDiff n).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_bound n x).1]; exact (cutoff_bound n x).2)

omit [μ.IsAddHaarMeasure] in
lemma cutoff_smul_converges {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖cutoff n x • f x-f x‖ ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖cutoff n x • f x-f x‖ ∂μ) atTop (𝓝 (∫ x, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro n; exact ((cutoff_smul_integrable hf n).sub hf).norm.aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _), show cutoff n x • f x-f x = (cutoff n x-1) • f x by rw [sub_smul,one_smul], norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (cutoff_bound n x).2)]
        nlinarith [(cutoff_bound n x).1,norm_nonneg (f x)])
    · exact ae_of_all _ (fun x => by
        have hh := ((cutoff_tendsto x).smul_const (f x)).sub (tendsto_const_nhds (x := f x)) |>.norm
        simpa only [one_smul,sub_self,norm_zero] using hh)
  simpa only [integral_zero] using ht

omit [μ.IsAddHaarMeasure] in
lemma cutoff_gradient_integrable {f : E → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => f x • gradient (cutoff (E := E) n) x) μ := by
  exact hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp ((cutoff_contDiff n).continuous_fderiv (by simp)))
    (by
      apply (cutoff_compact (E := E) n).fderiv ℝ |>.comp_left
      exact (InnerProductSpace.toDual ℝ E).symm.map_zero)

omit [μ.IsAddHaarMeasure] in
lemma cutoff_gradient_converges {f : E → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖f x • gradient (cutoff (E := E) n) x‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨L,hL,hb⟩ := cutoff_gradient_bound (E := E)
  have ht : Tendsto (fun n : ℕ => (L/((n:ℝ)+1)) * ∫ x, ‖f x‖ ∂μ) atTop (𝓝 0) := by
    have hh := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul L).mul_const (∫ x, ‖f x‖ ∂μ)
    simpa only [mul_zero,zero_mul,mul_one_div] using hh
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  rw [← integral_const_mul]
  apply integral_mono (cutoff_gradient_integrable hf n).norm (hf.norm.const_mul _)
  intro x
  dsimp only
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution

lemma integral_norm_sub_triangle {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f g h : α → F} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ‖f x-h x‖ ∂μ) ≤ (∫ x, ‖f x-g x‖ ∂μ)+(∫ x, ‖g x-h x‖ ∂μ) := by
  have he := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm) (fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def cutGradient (f : E → ℝ) (g : E → E) (n : ℕ) (x : E) : E :=
  cutoff n x • g x + f x • gradient (cutoff (E := E) n) x

omit [μ.IsAddHaarMeasure] in
lemma cutGradient_integrable {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (n : ℕ) :
    Integrable (cutGradient f g n) μ :=
  (cutoff_smul_integrable hg n).add (cutoff_gradient_integrable hf n)

omit [μ.IsAddHaarMeasure] in
lemma cutGradient_converges {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, ‖cutGradient f g n x-g x‖ ∂μ) atTop (𝓝 0) := by
  have ht := (cutoff_smul_converges hg).add (cutoff_gradient_converges hf)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ (by simpa only [zero_add] using ht)
  intro n
  have he := integral_add ((cutoff_smul_integrable hg n).sub hg).norm (cutoff_gradient_integrable hf n).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  apply integral_mono ((cutGradient_integrable hf hg n).sub hg).norm (((cutoff_smul_integrable hg n).sub hg).norm.add (cutoff_gradient_integrable hf n).norm)
  intro x
  change ‖cutoff n x • g x + f x • gradient (cutoff n) x - g x‖ ≤ ‖cutoff n x • g x - g x‖+‖f x • gradient (cutoff n) x‖
  simpa only [add_sub_right_comm] using norm_add_le (cutoff n x • g x-g x) (f x • gradient (cutoff n) x)

/-- Strong W11 density obtained by truncation and normalized mollification.
Both approximations are genuine functions, not distributions defined by a new axiom. -/
theorem exists_smooth_compact_approx {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (∫ x, ‖u x-f x‖ ∂μ) < ε ∧ (∫ x, ‖gradient u x-g x‖ ∂μ) < ε := by
  have h1 := (cutoff_smul_converges hf).eventually (gt_mem_nhds (half_pos hε))
  have h2 := (cutGradient_converges hf hg).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨n,hn1,hn2⟩ := (h1.and h2).exists
  let f' : E → ℝ := fun x => cutoff n x*f x
  let g' : E → E := cutGradient f g n
  have hf' : Integrable f' μ := cutoff_smul_integrable hf n
  have hg' : Integrable g' μ := cutGradient_integrable hf hg n
  have hw' : HasGradient (μ := μ) f' g' := hw.mul_contDiff hf hg (cutoff_contDiff n) (cutoff_compact n)
  have hk1 := (smoothVector_converges hf').eventually (gt_mem_nhds (half_pos hε))
  have hk2 := (smoothVector_converges hg').eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨k,hk1,hk2⟩ := (hk1.and hk2).exists
  refine ⟨smooth (μ := μ) f' k, smoothVector_contDiff hf' k, ?_, ?_, ?_⟩
  · exact (mollifier k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) (cutoff_compact n).mul_right
  · have hi := integral_norm_sub_triangle (smoothVector_integrable hf' k) hf' hf
    change (∫ x, ‖f' x-f x‖ ∂μ) < ε/2 at hn1
    change (∫ x, ‖smoothVector (μ := μ) f' k x-f x‖ ∂μ) < ε
    linarith
  · rw [smooth_gradient hf' hg' hw']
    have hi := integral_norm_sub_triangle (smoothVector_integrable hg' k) hg' hg
    change (∫ x, ‖g' x-g x‖ ∂μ) < ε/2 at hn2
    linarith

end WeakSobolev

namespace WeakSobolev
section L1
variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {f : α → F} {u : ℕ → α → F}

lemma tendsto_eLpNorm_one (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n-f) 1 μ) atTop (𝓝 0) := by
  have he (n) : eLpNorm (u n-f) 1 μ = ENNReal.ofReal (∫ x, ‖u n x-f x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hu n).sub hf).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hu n).sub hf)]
    rfl
  simp_rw [he]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim

lemma integral_converges_norm [NormedSpace ℝ F]
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_L1' f (Eventually.of_forall hu) (tendsto_eLpNorm_one hf hu hlim)

lemma exists_ae_subseq (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂μ, Tendsto (fun n => u (s n) x) atTop (𝓝 (f x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (tendsto_eLpNorm_one hf hu hlim)).exists_seq_tendsto_ae

lemma bounded_smul_converges [NormedSpace ℝ F]
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0))
    {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {K : ℝ} (hK : ∀ᵐ x ∂μ, ‖φ x‖ ≤ K) :
    Tendsto (fun n => ∫ x, ‖φ x • u n x - φ x • f x‖ ∂μ) atTop (𝓝 0) := by
  have ht := hlim.const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun x => norm_nonneg _))) _ (by simpa only [mul_zero] using ht)
  exact Eventually.of_forall (fun n => by
    rw [← integral_const_mul]
    apply integral_mono_ae (( (hu n).bdd_smul K hφ hK).sub (hf.bdd_smul K hφ hK)).norm (((hu n).sub hf).norm.const_mul K)
    filter_upwards [hK] with x hx
    change ‖φ x • u n x-φ x • f x‖ ≤ K*‖u n x-f x‖
    rw [← smul_sub,norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
end L1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

omit [BorelSpace E] in
lemma integral_inner_mul {φ : E → ℝ} {g : E → E}
    (hi : Integrable (fun x => φ x • g x) μ) (v : E) :
    (∫ x, ⟪g x,v⟫*φ x ∂μ) = ⟪∫ x, φ x • g x ∂μ,v⟫ := by
  rw [real_inner_comm,← integral_inner (𝕜 := ℝ) hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [real_inner_smul_right,real_inner_comm]; ring)

/-- The distributional identity is closed under strong L1 convergence of both
functions and their genuine gradients. -/
lemma HasGradient.limit {f : E → ℝ} {g : E → E} {u : ℕ → E → ℝ} {v : ℕ → E → E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hu : ∀ n, Integrable (u n) μ) (hv : ∀ n, Integrable (v n) μ)
    (hw : ∀ n, HasGradient (μ := μ) (u n) (v n))
    (huf : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => ∫ x, ‖v n x-g x‖ ∂μ) atTop (𝓝 0)) :
    HasGradient (μ := μ) f g := by
  intro φ hφ hc e
  let d : E → ℝ := fun x => fderiv ℝ φ x e
  have hd : Continuous d := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ e
  obtain ⟨D,hD⟩ := hd.norm.bddAbove_range_of_hasCompactSupport hdc.norm
  obtain ⟨K,hK⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hDb : ∀ᵐ x ∂μ, ‖d x‖ ≤ D := ae_of_all _ (fun x => hD (mem_range_self x))
  have hKb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ K := ae_of_all _ (fun x => hK (mem_range_self x))
  have ht1 := integral_converges_norm (hf.bdd_smul D hd.aestronglyMeasurable hDb)
    (fun n => (hu n).bdd_smul D hd.aestronglyMeasurable hDb)
    (bounded_smul_converges hf hu huf hd.aestronglyMeasurable hDb)
  have ht2 := integral_converges_norm (hg.bdd_smul K hφ.continuous.aestronglyMeasurable hKb)
    (fun n => (hv n).bdd_smul K hφ.continuous.aestronglyMeasurable hKb)
    (bounded_smul_converges hg hv hvg hφ.continuous.aestronglyMeasurable hKb)
  have he (n : ℕ) : (∫ x, d x • u n x ∂μ) = -⟪∫ x, φ x • v n x ∂μ,e⟫ := by
    rw [← integral_inner_mul ((hv n).bdd_smul K hφ.continuous.aestronglyMeasurable hKb)]
    simpa only [d,smul_eq_mul,mul_comm] using hw n φ hφ hc e
  have ht3 := (ht2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := e))).neg
  have h := tendsto_nhds_unique ht1 (ht3.congr (fun n => (he n).symm))
  change (∫ x, d x • f x ∂μ) = -⟪∫ x, φ x • g x ∂μ,e⟫ at h
  rw [← integral_inner_mul (hg.bdd_smul K hφ.continuous.aestronglyMeasurable hKb)] at h
  simpa only [d,smul_eq_mul,mul_comm] using h

end WeakSobolev

namespace WeakSobolev
section Coefficients
variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {g : α → F} {v : ℕ → α → F}
lemma varying_smul_converges
    (hg : Integrable g μ) (hv : ∀ n, Integrable (v n) μ)
    (hvg : Tendsto (fun n => ∫ x, ‖v n x-g x‖ ∂μ) atTop (𝓝 0))
    {c : α → ℝ} {d : ℕ → α → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (hc : AEStronglyMeasurable c μ) (hd : ∀ n, AEStronglyMeasurable (d n) μ)
    (hcb : ∀ᵐ x ∂μ, ‖c x‖ ≤ K) (hdb : ∀ n, ∀ᵐ x ∂μ, ‖d n x‖ ≤ K)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => d n x) atTop (𝓝 (c x))) :
    Tendsto (fun n => ∫ x, ‖d n x • v n x-c x • g x‖ ∂μ) atTop (𝓝 0) := by
  have hi (n) : Integrable (fun x => ‖(d n x-c x) • g x‖) μ :=
    ((hg.bdd_smul K (hd n) (hdb n)).sub (hg.bdd_smul K hc hcb)).norm.congr
      (ae_of_all _ (fun x => by dsimp only; rw [sub_smul]; rfl))
  have ht1 : Tendsto (fun n => ∫ x, ‖(d n x-c x) • g x‖ ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => 2*K*‖g x‖)
      (fun n => (hi n).aestronglyMeasurable) (hg.norm.const_mul (2*K))
      (fun n => by
        filter_upwards [hdb n,hcb] with x hx hy
        rw [norm_norm,norm_smul]
        exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _))
      (hlim.mono (fun x hx => by simpa using ((hx.sub tendsto_const_nhds).smul_const (g x)).norm))
    simpa using ht
  have ht2 : Tendsto (fun n => K*(∫ x, ‖v n x-g x‖ ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hvg.const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun x => norm_nonneg _))) _ (by simpa only [zero_add] using ht1.add ht2)
  exact Eventually.of_forall (fun n => by
    have he := integral_add (hi n) (((hv n).sub hg).norm.const_mul K)
    simp only [Pi.sub_apply] at he
    rw [← integral_const_mul,← he]
    apply integral_mono_ae (((hv n).bdd_smul K (hd n) (hdb n)).sub (hg.bdd_smul K hc hcb)).norm
      ((hi n).add (((hv n).sub hg).norm.const_mul K))
    filter_upwards [hdb n] with x hx
    change ‖d n x • v n x-c x • g x‖ ≤ ‖(d n x-c x) • g x‖+K*‖v n x-g x‖
    calc
      _ = ‖(d n x-c x) • g x+d n x • (v n x-g x)‖ := by congr 1; module
      _ ≤ ‖(d n x-c x) • g x‖+‖d n x • (v n x-g x)‖ := norm_add_le _ _
      _ ≤ _ := by
        have hh : ‖d n x • (v n x-g x)‖ ≤ K*‖v n x-g x‖ := by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        exact add_le_add le_rfl hh)
end Coefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma exists_smooth_sequence {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g) :
    ∃ u : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖gradient (u n) x-g x‖ ∂μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) := by
  have hex (n : ℕ) := exists_smooth_compact_approx hf hg hw (by positivity : 0 < 1/((n:ℝ)+1))
  choose u hu hc hf' hg' using hex
  have ht : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht1 := squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) (fun n => (hf' n).le) ht
  have ht2 := squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) (fun n => (hg' n).le) ht
  have hi (n) : Integrable (u n) μ := (hu n).continuous.integrable_of_hasCompactSupport (hc n)
  obtain ⟨s,hs,ha⟩ := exists_ae_subseq hf hi ht1
  exact ⟨fun n => u (s n),fun n => ⟨hu _,hc _⟩,ht1.comp hs.tendsto_atTop,ht2.comp hs.tendsto_atTop,ha⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_scalar_comp {u : E → ℝ} {Φ : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hΦ : Differentiable ℝ Φ) (x : E) :
    gradient (Φ ∘ u) x = deriv Φ (u x) • gradient u x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [fderiv_comp x (hΦ _) (hu _)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [(hΦ _).hasDerivAt.hasFDerivAt.fderiv]
  change fderiv ℝ u x v * deriv Φ (u x) = deriv Φ (u x) * fderiv ℝ u x v
  ring

lemma HasGradient.scalar_comp {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {K : ℝ≥0} (hK : LipschitzWith K Φ) (h0 : Φ 0 = 0) :
    HasGradient (μ := μ) (Φ ∘ f) (fun x => deriv Φ (f x) • g x) := by
  obtain ⟨u,hu,huf,hvg,ha⟩ := exists_smooth_sequence hf hg hw
  have hi (n) : Integrable (u n) μ := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hgi (n) : Integrable (gradient (u n)) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp ((hu n).1.continuous_fderiv (by simp))).integrable_of_hasCompactSupport
      (((hu n).2.fderiv ℝ).comp_left (map_zero _))
  have hid : Integrable (Φ ∘ f) μ := memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr hf))
  have hδ := hΦ.continuous_deriv le_rfl
  have hδb (x : ℝ) : ‖deriv Φ x‖ ≤ (K:ℝ) := norm_deriv_le_of_lipschitz hK
  have hgrad : Integrable (fun x => deriv Φ (f x) • g x) μ :=
    hg.bdd_smul K (hδ.comp_aestronglyMeasurable hf.aestronglyMeasurable) (ae_of_all _ (fun x => hδb _))
  have hvi (n) : Integrable (fun x => deriv Φ (u n x) • gradient (u n) x) μ :=
    (hgi n).bdd_smul K ((hδ.comp (hu n).1.continuous).aestronglyMeasurable) (ae_of_all _ (fun x => hδb _))
  apply HasGradient.limit (u := fun n => Φ ∘ u n) (v := fun n x => deriv Φ (u n x) • gradient (u n) x) hid hgrad (fun n => memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr (hi n)))) hvi
  · intro n
    exact (contDiff_hasGradient (μ := μ) (hΦ.comp ((hu n).1.of_le (by simp)))).congr_ae
      (EventuallyEq.rfl) (ae_of_all _ (fun x => gradient_scalar_comp ((hu n).1.differentiable (by simp)) (hΦ.differentiable one_ne_zero) x))
  · apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ (by simpa only [mul_zero] using huf.const_mul (K:ℝ))
    intro n
    rw [← integral_const_mul]
    exact integral_mono ((memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr (hi n)))).sub hid).norm
      (((hi n).sub hf).norm.const_mul (K:ℝ)) (fun x => hK.norm_sub_le _ _)
  · exact varying_smul_converges hg hgi hvg K.coe_nonneg
      (hδ.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (fun n => (hδ.comp (hu n).1.continuous).aestronglyMeasurable)
      (ae_of_all _ (fun x => hδb _)) (fun n => ae_of_all _ (fun x => hδb _))
      (ha.mono (fun x hx => (hδ.tendsto _).comp hx))
end WeakSobolev

namespace WeakSobolev
/-- Smooth absolute-value approximation with zero preserved. -/
def smoothAbs (ε x : ℝ) : ℝ := Real.sqrt (x^2+ε^2)-ε
lemma smoothAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (smoothAbs ε) := by
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt (fun x => ne_of_gt (by positivity)) |>.sub contDiff_const
lemma smoothAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (smoothAbs ε) (x/Real.sqrt (x^2+ε^2)) x := by
  have he : x^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hd := ((((hasDerivAt_id x).pow 2).add_const (ε^2)).sqrt he).sub_const ε
  change HasDerivAt (fun y => Real.sqrt (y^2+ε^2)-ε) _ x
  simpa [mul_div_mul_left x (Real.sqrt (x^2+ε^2)) (by norm_num : (2:ℝ) ≠ 0)] using hd
lemma smoothAbs_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (smoothAbs ε) x = x/Real.sqrt (x^2+ε^2) := (smoothAbs_hasDerivAt hε x).deriv
lemma smoothAbs_deriv_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖deriv (smoothAbs ε) x‖ ≤ 1 := by
  rw [smoothAbs_deriv hε,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  rw [one_mul]
  have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) : x^2 ≤ x^2+ε^2)
  simpa only [Real.sqrt_sq_eq_abs] using h
lemma smoothAbs_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (smoothAbs ε) :=
  lipschitzWith_of_nnnorm_deriv_le (fun x => (smoothAbs_hasDerivAt hε x).differentiableAt)
    (fun x => by exact_mod_cast smoothAbs_deriv_bound hε x)
lemma smoothAbs_zero {ε : ℝ} (hε : 0 ≤ ε) : smoothAbs ε 0 = 0 := by
  simp [smoothAbs,Real.sqrt_sq,hε]
lemma smoothAbs_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ‖smoothAbs ε x‖ ≤ ‖x‖ := by
  simpa only [smoothAbs_zero hε.le,sub_zero,NNReal.coe_one,one_mul] using (smoothAbs_lipschitz hε).norm_sub_le x 0
lemma smoothAbs_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => smoothAbs (1/((n:ℝ)+1)) x) atTop (𝓝 |x|) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht := ((tendsto_const_nhds (x := x^2)).add (h.pow 2)).sqrt |>.sub h
  simpa only [smoothAbs,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,sub_zero,Real.sqrt_sq_eq_abs] using ht

def absCoefficient (x : ℝ) : ℝ := x/|x|
lemma absCoefficient_bound (x : ℝ) : ‖absCoefficient x‖ ≤ 1 := by
  by_cases hx : x=0
  · simp [absCoefficient,hx]
  · simp [absCoefficient,Real.norm_eq_abs,abs_abs,abs_ne_zero.mpr hx]
lemma absCoefficient_measurable : Measurable absCoefficient := measurable_id.div measurable_id.abs
lemma smoothAbs_deriv_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => deriv (smoothAbs (1/((n:ℝ)+1))) x) atTop (𝓝 (absCoefficient x)) := by
  have he (n : ℕ) : deriv (smoothAbs (1/((n:ℝ)+1))) x = x/Real.sqrt (x^2+(1/((n:ℝ)+1))^2) := smoothAbs_deriv (by positivity) x
  simp_rw [he]
  by_cases hx : x=0
  · simp [hx,absCoefficient]
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht := (tendsto_const_nhds (x := x)).div (((tendsto_const_nhds (x := x^2)).add (h.pow 2)).sqrt)
      (by simpa only [zero_pow (by norm_num : (2:ℕ) ≠0),add_zero,Real.sqrt_sq_eq_abs] using abs_ne_zero.mpr hx)
    change Tendsto (fun n : ℕ => x / Real.sqrt (x^2+(1/((n:ℝ)+1))^2)) atTop
      (𝓝 (x / Real.sqrt (x^2+0^2))) at ht
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠0),add_zero,Real.sqrt_sq_eq_abs,absCoefficient] using ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma HasGradient.abs {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g) :
    HasGradient (μ := μ) (fun x => |f x|) (fun x => absCoefficient (f x) • g x) := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hc : AEStronglyMeasurable (fun x => absCoefficient (f x)) μ :=
    (absCoefficient_measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  have hcb : ∀ᵐ x ∂μ, ‖absCoefficient (f x)‖ ≤ (1:ℝ) := ae_of_all _ (fun x => absCoefficient_bound _)
  have hi (n) : Integrable (smoothAbs (ε n) ∘ f) μ :=
    memLp_one_iff_integrable.mp ((smoothAbs_lipschitz (hε n)).comp_memLp (smoothAbs_zero (hε n).le) (memLp_one_iff_integrable.mpr hf))
  have hv (n) : Integrable (fun x => deriv (smoothAbs (ε n)) (f x) • g x) μ :=
    hg.bdd_smul 1 (((smoothAbs_contDiff (hε n)).continuous_deriv le_rfl).comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ (fun x => smoothAbs_deriv_bound (hε n) _))
  apply HasGradient.limit (u := fun n => smoothAbs (ε n) ∘ f)
    (v := fun n x => deriv (smoothAbs (ε n)) (f x) • g x) hf.abs (hg.bdd_smul 1 hc hcb) hi hv
  · intro n
    exact hw.scalar_comp hf hg (smoothAbs_contDiff (hε n)) (smoothAbs_lipschitz (hε n)) (smoothAbs_zero (hε n).le)
  · have ht := tendsto_integral_of_dominated_convergence (fun x => 2*‖f x‖)
      (fun n => ((hi n).sub hf.abs).norm.aestronglyMeasurable) (hf.norm.const_mul 2)
      (fun n => ae_of_all _ (fun x => by
        change ‖‖smoothAbs (ε n) (f x)-|f x|‖‖ ≤ 2*‖f x‖
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs,abs_abs,two_mul] using add_le_add (smoothAbs_bound (hε n) (f x)) (le_refl |f x|))))
      (ae_of_all _ (fun x => by simpa only [ε,Function.comp_apply,Pi.sub_apply,sub_self,norm_zero] using ((smoothAbs_tendsto (f x)).sub (tendsto_const_nhds (x := |f x|))).norm))
    simpa using ht
  · apply varying_smul_converges hg (fun _ => hg) (by simp) zero_le_one hc
      (fun n => ((smoothAbs_contDiff (hε n)).continuous_deriv le_rfl).comp_aestronglyMeasurable hf.aestronglyMeasurable)
      hcb (fun n => ae_of_all _ (fun x => smoothAbs_deriv_bound (hε n) _))
    exact ae_of_all _ (fun x => smoothAbs_deriv_tendsto (f x))

omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma abs_gradient_bound {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => absCoefficient (f x) • g x) μ ∧
      (∫ x, ‖absCoefficient (f x) • g x‖ ∂μ) ≤ ∫ x, ‖g x‖ ∂μ := by
  have hi := hg.bdd_smul 1 ((absCoefficient_measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable)
    (ae_of_all _ (fun x => absCoefficient_bound (f x)))
  refine ⟨hi,integral_mono hi.norm hg.norm (fun x => ?_)⟩
  rw [norm_smul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (absCoefficient_bound (f x)) (norm_nonneg (g x))
end WeakSobolev

end

end OAI
