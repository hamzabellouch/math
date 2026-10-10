import OAI.Analysis.Steinitz.GaussianKernel

namespace OAI

/-! Heat operators, weak coordinate derivatives, and Dirichlet energy. -/

section

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma memLp_mul_bounded (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    MemLp (fun x => m x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C) (hm.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hb] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

noncomputable def mulLp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_mul_bounded m hm hb f).toLp _

lemma mulLp_coe (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulLp m hm hb f : X → ℂ) =ᵐ[μ] fun x => m x * f x := MemLp.coeFn_toLp _

noncomputable def mulLinear (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLp m hm hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [mulLp_coe m hm hb (f+g), mulLp_coe m hm hb f,
      mulLp_coe m hm hb g, Lp.coeFn_add f g, Lp.coeFn_add (mulLp m hm hb f) (mulLp m hm hb g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₄, h₅, h₂, h₃, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [mulLp_coe m hm hb (c • f), mulLp_coe m hm hb f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLp m hm hb f)] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
    simp only [RingHom.id_apply]
    rw [h₁, h₃, h₄, h₂]
    ring

lemma mulLp_norm_le (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖mulLp m hm hb f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulLp_coe m hm hb f, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

noncomputable def mulOp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulLinear m hm hb).mkContinuous C (mulLp_norm_le m hm hb)

lemma mulOp_coe (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulOp m hm hb f : X → ℂ) =ᵐ[μ] fun x => m x * f x := mulLp_coe m hm hb f

lemma mulOp_norm_le (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : ‖mulOp m hm hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have he := L2.inner_def (𝕜 := ℂ) f f
  simp only [inner_self_eq_norm_sq_to_K] at he
  change (‖f‖ : ℂ)^2 = ∫ x, (‖f x‖ : ℂ)^2 ∂μ at he
  simp only [← Complex.ofReal_pow, integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

lemma inner_mulOp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f g : Lp ℂ 2 μ) :
    ⟪f, mulOp m hm hb g⟫ = ∫ x, m x * (g x * conj (f x)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulOp_coe m hm hb g] with x hx
  rw [hx]
  simp only [RCLike.inner_apply]
  ring

lemma inner_real_mulOp (m : X → ℝ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖(m x : ℂ)‖ ≤ C) (f : Lp ℂ 2 μ) :
    (⟪f, mulOp (fun x => (m x : ℂ)) (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) hb f⟫).re =
      ∫ x, m x * ‖f x‖^2 ∂μ := by
  rw [inner_mulOp]
  have he : (fun x => (m x : ℂ) * (f x * conj (f x))) =
      fun x => ((m x * ‖f x‖^2 : ℝ) : ℂ) := by
    ext x
    rw [RCLike.mul_conj]
    simp
  rw [he, integral_complex_ofReal]
  rfl

end Multiplier
end HeatL2

namespace HeatL2
section Translation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def translate (a : E) : Lp ℂ 2 (volume : Measure E) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a) (measurePreserving_add_right volume a)

lemma translate_coe (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    (translate a f : E → ℂ) =ᵐ[volume] fun x => f (x+a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)

noncomputable def phase (a ξ : E) : ℂ := Real.fourierChar (inner ℝ a ξ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_continuous (a : E) : Continuous (phase a) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).comp (continuous_const.inner continuous_id)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_norm (a ξ : E) : ‖phase a ξ‖ = 1 := Circle.norm_coe _

noncomputable def phaseOp (a : E) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  mulOp (phase a) (phase_continuous a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => (phase_norm a ξ).le)

lemma phaseOp_coe (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    (phaseOp a f : E → ℂ) =ᵐ[volume] fun ξ => phase a ξ * (f : E → ℂ) ξ :=
  mulOp_coe _ _ _ _

lemma translate_schwartz (a : E) (f : SchwartzMap E ℂ) :
    translate a (f.toLp 2) = (SchwartzMap.compSubConstCLM ℂ (-a) f).toLp 2 := by
  apply Lp.ext
  filter_upwards [translate_coe a (f.toLp 2),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2),
    (SchwartzMap.compSubConstCLM ℂ (-a) f).coeFn_toLp 2] with x h₁ h₂ h₃
  simpa only [h₁, h₃, Function.comp_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using h₂

lemma schwartz_fourier_translate (a : E) (f : SchwartzMap E ℂ) :
    ∀ ξ, (𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) f)) ξ = phase a ξ * (𝓕 f) ξ := by
  intro ξ
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ E) (f : E → ℂ) a) ξ
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • f (x+a)) = _ at he
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • f (x - -a)) =
    phase a ξ * (∫ x, Real.fourierChar (-inner ℝ x ξ) • f x)
  simpa only [sub_neg_eq_add, Circle.smul_def, smul_eq_mul, phase, innerₗ_apply_apply,
    VectorFourier.fourierIntegral] using he

lemma fourier_translate (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    𝓕 (translate a f) = phaseOp a (𝓕 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := (volume : Measure E)) ENNReal.ofNat_ne_top).induction_on
    (p := fun g => 𝓕 (translate a g) = phaseOp a (𝓕 g)) f ?_ ?_
  · exact isClosed_eq (continuous_fourier.comp (translate a).continuous)
      ((phaseOp a).continuous.comp continuous_fourier)
  · intro g
    change 𝓕 (translate a (g.toLp 2)) = phaseOp a (𝓕 (g.toLp 2))
    rw [translate_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) g)).coeFn_toLp 2,
      phaseOp_coe a ((𝓕 g).toLp 2),
      (𝓕 g).coeFn_toLp 2] with ξ h₁ h₂ h₃
    rw [h₁, h₂, h₃, schwartz_fourier_translate]

lemma translate_sub_norm_sq (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate a f - f‖^2 = ∫ ξ, ‖phase a ξ - 1‖^2 * ‖(𝓕 f) ξ‖^2 := by
  have hs : 𝓕 (translate a f - f) = 𝓕 (translate a f) - 𝓕 f :=
    (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _
  rw [← Lp.norm_fourier_eq (translate a f - f), hs, fourier_translate,
    norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (phaseOp a (𝓕 f)) (𝓕 f),
    phaseOp_coe a (𝓕 f)] with ξ h₁ h₂
  simp only [Pi.sub_apply] at h₁
  rw [h₁, h₂, ← sub_one_mul, norm_mul, mul_pow]

end Translation
end HeatL2

namespace HeatL2
section TranslationContinuous
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma translate_sub_translate_norm_sq (a b : E) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate a f - translate b f‖^2 =
      ∫ ξ, ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2 := by
  have hs : 𝓕 (translate a f - translate b f) = 𝓕 (translate a f) - 𝓕 (translate b f) :=
    (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _
  rw [← Lp.norm_fourier_eq (translate a f - translate b f), hs, fourier_translate,
    fourier_translate, norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (phaseOp a (𝓕 f)) (phaseOp b (𝓕 f)),
    phaseOp_coe a (𝓕 f),
    phaseOp_coe b (𝓕 f)] with ξ h₁ h₂ h₃
  simp only [Pi.sub_apply] at h₁
  rw [h₁, h₂, h₃, ← sub_mul, norm_mul, mul_pow]

lemma translate_continuous (f : Lp ℂ 2 (volume : Measure E)) :
    Continuous (fun a : E => translate a f) := by
  rw [continuous_iff_continuousAt]
  intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun a : E => ‖translate a f - translate b f‖^2) (𝓝 b) (𝓝 0) := by
    simp_rw [translate_sub_translate_norm_sq]
    have hi := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure E)) (l := 𝓝 b)
      (F := fun a ξ => ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2)
      (f := fun _ => (0 : ℝ)) (fun ξ => 4 * ‖(𝓕 f) ξ‖^2)
    apply (by simpa using hi : _)
    · exact Filter.Eventually.of_forall fun a =>
        (((phase_continuous a).sub (phase_continuous b)).norm.pow 2).aestronglyMeasurable.mul
          ((Lp.aestronglyMeasurable (𝓕 f)).norm.pow 2)
    · apply Filter.Eventually.of_forall
      intro a
      apply Filter.Eventually.of_forall
      intro ξ
      have hn : ‖phase a ξ - phase b ξ‖ ≤ 2 := by
        calc
          _ ≤ ‖phase a ξ‖ + ‖phase b ξ‖ := norm_sub_le _ _
          _ = 2 := by rw [phase_norm, phase_norm]; norm_num
      have hs : ‖phase a ξ - phase b ξ‖^2 ≤ 4 := by nlinarith [norm_nonneg (phase a ξ-phase b ξ)]
      simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
        mul_le_mul_of_nonneg_right hs (sq_nonneg ‖(𝓕 f) ξ‖)
    · exact ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul 4
    · apply Filter.Eventually.of_forall
      intro ξ
      have hc : Continuous (fun a : E => phase a ξ) :=
        (continuous_subtype_val.comp Real.continuous_fourierChar).comp
          (continuous_id.inner continuous_const)
      have hc' : Continuous (fun a : E => ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2) :=
        ((hc.sub continuous_const).norm.pow 2).mul continuous_const
      simpa using hc'.tendsto b
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using
    (Real.continuous_sqrt.tendsto 0).comp ht

end TranslationContinuous
end HeatL2

namespace HeatL2
section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_weight (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hb : ∀ᵐ x ∂volume, |m x| ≤ C) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun x => m x * ‖f x‖^2) := by
  apply Integrable.mono' (((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul C)
    (hm.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
  filter_upwards [hb] with x hx
  simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
    mul_le_mul_of_nonneg_right hx (sq_nonneg ‖f x‖)

noncomputable def spectralOp (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (mulOp (fun x => (m x : ℂ)) (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
      (Filter.Eventually.of_forall fun x => by simpa using hb x)) ∘L
    (Lp.fourierTransformₗᵢ E ℂ).toContinuousLinearEquiv.toContinuousLinearMap

lemma spectralOp_fourier (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    (fun x => (𝓕 (spectralOp m hm hb f) : Lp ℂ 2 (volume : Measure E)) x) =ᵐ[volume] fun x => (m x : ℂ) * (𝓕 f) x := by
  change ((Lp.fourierTransformₗᵢ E ℂ) ((Lp.fourierTransformₗᵢ E ℂ).symm _) : E → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact mulOp_coe (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) (C := 1)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)

lemma spectralOp_norm_le (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖spectralOp m hm hb f‖ ≤ ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ E ℂ).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖mulOp (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)‖ ≤ ‖f‖
  exact (mulLp_norm_le (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) (C := 1)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)).trans_eq (by simp)

lemma spectralOp_inner (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    ⟪f, spectralOp m hm hb f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  have he : (fun x => inner ℂ ((𝓕 f) x) ((𝓕 (spectralOp m hm hb f)) x)) =ᵐ[volume]
      fun x => ((m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    filter_upwards [spectralOp_fourier m hm hb f] with x hx
    rw [hx]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, RCLike.mul_conj]
    simp
  rw [integral_congr_ae he, integral_complex_ofReal]

lemma spectralOp_positive (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (hn : ∀ x, 0 ≤ m x) :
    (spectralOp m hm hb).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have he : ⟪spectralOp m hm hb f, f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, spectralOp_inner]
    simp
  rw [he]
  exact ⟨rfl, integral_nonneg fun x => mul_nonneg (hn x) (sq_nonneg _)⟩

noncomputable def heat (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  spectralOp (fun x => Real.exp (-w x)) (Real.continuous_exp.comp_aestronglyMeasurable hw.neg)
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))

noncomputable def energy (w : E → ℝ) (f : Lp ℂ 2 (volume : Measure E)) : ℝ :=
  ∫ x, (1-Real.exp (-w x)) * ‖(𝓕 f) x‖^2

lemma heat_inner (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, heat w hw hn f⟫).re = ‖f‖^2 - energy w f := by
  rw [heat, spectralOp_inner]
  simp only [Complex.ofReal_re]
  have hb : ∀ x, |1-Real.exp (-w x)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x))))]
    linarith [Real.exp_pos (-w x)]
  have hint : Integrable (fun x => (1-Real.exp (-w x)) * ‖(𝓕 f) x‖^2) :=
    integrable_weight (fun x => 1-Real.exp (-w x))
      (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
      (Filter.Eventually.of_forall hb) (𝓕 f)
  rw [energy, ← Lp.norm_fourier_eq f, norm_sq_integral,
    ← integral_sub ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      hint]
  congr 1
  ext x
  ring

lemma energy_nonneg (w : E → ℝ) (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    0 ≤ energy w f := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))) (sq_nonneg _)

end Spectral
end HeatL2
namespace HeatL2
noncomputable def loss (x : ℝ) : ℝ := 1 - Real.exp (-x)

lemma loss_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ loss x := by
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))

lemma loss_le_one (x : ℝ) : loss x ≤ 1 := by
  unfold loss
  linarith [Real.exp_pos (-x)]

lemma loss_le_self (x : ℝ) : loss x ≤ x := by
  unfold loss
  linarith [Real.add_one_le_exp (-x)]

lemma loss_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    loss (x+y) ≤ loss x + loss y := by
  have hp := mul_nonneg (loss_nonneg hx) (loss_nonneg hy)
  simp only [loss, neg_add, Real.exp_add] at *
  nlinarith

lemma loss_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    loss (∑ i ∈ s, a i) ≤ ∑ i ∈ s, loss (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [loss]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (loss_add_le (ha i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj))).trans
      (add_le_add_right (ih fun j hj => ha j (Finset.mem_insert_of_mem hj)) _)

lemma loss_dilate_le {c x : ℝ} (hc : 1 ≤ c) : loss (c*x) ≤ c*loss x := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hci : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hci1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have he := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-c*x))
    (sub_nonneg.mpr hci1) hci.le (by ring : 1-c⁻¹+c⁻¹ = 1)
  have harg : (1-c⁻¹)*(0:ℝ) + c⁻¹*(-c*x) = -x := by field_simp; ring
  simp only [smul_eq_mul, harg, Real.exp_zero, mul_one] at he
  have hm := mul_le_mul_of_nonneg_left he hcpos.le
  rw [loss, loss]
  have hcc : c*c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
  simp only [mul_add, mul_sub, mul_one, ← mul_assoc, hcc, one_mul, neg_mul] at hm
  linarith

lemma loss_sum_dilate_le {ι : Type*} (s : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ s, 1 ≤ c i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    loss (∑ i ∈ s, c i*x i) ≤ ∑ i ∈ s, c i*loss (x i) := by
  exact (loss_sum_le s _ (fun i hi => mul_nonneg (le_trans zero_le_one (hc i hi)) (hx i hi))).trans
    (Finset.sum_le_sum fun i hi => loss_dilate_le (hc i hi))

lemma loss_mean_ge {ι : Type*} (s : Finset ι) (q x : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i = 1) :
    ∑ i ∈ s, q i*loss (x i) ≤ loss (∑ i ∈ s, q i*x i) := by
  have he := convexOn_exp.map_sum_le hq hs (fun i hi => Set.mem_univ (-x i))
  simp only [smul_eq_mul] at he
  have hneg : (∑ i ∈ s, q i * -x i) = -(∑ i ∈ s, q i*x i) := by simp [Finset.sum_neg_distrib]
  rw [hneg] at he
  simp only [loss, mul_sub, mul_one, Finset.sum_sub_distrib, hs]
  linarith

lemma loss_lower {x : ℝ} (hx : 0 ≤ x) : x/(1+x) ≤ loss x := by
  have hp : 0 < 1+x := by linarith
  have he : Real.exp (-x) ≤ (1+x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) hp).mpr (by linarith [Real.add_one_le_exp x])
  rw [loss, div_le_iff₀ hp]
  have hmul := mul_le_mul_of_nonneg_right he hp.le
  rw [inv_mul_cancel₀ hp.ne'] at hmul
  nlinarith

lemma bound_by_loss {A H η z : ℝ} (hH : 0 ≤ H) (hη : 0 < η)
    (hz : 0 ≤ z) (h₁ : A ≤ H*z) (h₂ : A ≤ 4) :
    A ≤ (H+4*η)/η * loss (η*z) := by
  have hp : 0 < 1+η*z := by positivity
  have hlow := loss_lower (mul_nonneg hη.le hz)
  have hc : 0 ≤ (H+4*η)/η := by positivity
  have he : A ≤ (H+4*η)/η * (η*z/(1+η*z)) := by
    have hr : (H+4*η)/η * (η*z/(1+η*z)) = (H*z+4*η*z)/(1+η*z) := by
      field_simp
    rw [hr, le_div_iff₀ hp]
    have hm := mul_le_mul_of_nonneg_right h₂ (mul_nonneg hη.le hz)
    nlinarith
  exact he.trans (mul_le_mul_of_nonneg_left hlow hc)

end HeatL2

namespace HeatL2
section Mask
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
lemma indicator_one_norm_le (D : Set X) (x : X) : ‖D.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ D <;> simp [hx]

noncomputable def mask (D : Set X) (hD : MeasurableSet D) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulOp (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D))

lemma mask_coe (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    (mask D hD f : X → ℂ) =ᵐ[μ] D.indicator f := by
  filter_upwards [mulOp_coe (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f] with x hx
  change mulOp _ _ _ f x = _
  rw [hx]
  classical
  by_cases hx : x ∈ D <;> simp [hx]

lemma mask_norm_le (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    ‖mask D hD f‖ ≤ ‖f‖ := by
  apply le_trans (mulLp_norm_le (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f)
  simp only [one_mul, le_refl]

lemma mask_idempotent (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD (mask D hD f) = mask D hD f := by
  apply Lp.ext
  filter_upwards [mask_coe D hD (mask D hD f), mask_coe D hD f] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp_all

lemma mask_inner (D : Set X) (hD : MeasurableSet D) (f g : Lp ℂ 2 μ) :
    ⟪mask D hD f, g⟫ = ⟪f, mask D hD g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mask_coe D hD f, mask_coe D hD g] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp [h₁, h₂, hx]

lemma mask_adjoint (D : Set X) (hD : MeasurableSet D) :
    (mask (μ := μ) D hD).adjoint = mask D hD := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (mask_inner D hD f g).symm

noncomputable def supported (D : Set X) : Set (Lp ℂ 2 μ) :=
  {f | ∀ᵐ x ∂μ, x ∉ D → f x = 0}

lemma mask_eq_self_iff (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD f = f ↔ f ∈ supported D := by
  classical
  constructor
  · intro h
    have hc := mask_coe D hD f
    rw [h] at hc
    filter_upwards [hc] with x hx hnot
    simpa [hnot] using hx
  · intro h
    apply Lp.ext
    filter_upwards [mask_coe D hD f, h] with x hx hs
    by_cases hmem : x ∈ D <;> simp [hx, hmem, hs]

end Mask

section PositiveNorm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma positive_norm_le_iff (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ} (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ f, (⟪f, T f⟫).re ≤ C * ‖f‖^2 := by
  constructor
  · intro h f
    have he := (Complex.re_le_norm ⟪f, T f⟫).trans (norm_inner_le_norm f (T f))
    have hn := T.le_opNorm f
    have hm := mul_le_mul_of_nonneg_left (hn.trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg f))) (norm_nonneg f)
    nlinarith
  · intro h
    rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
    apply ciSup_le
    intro f
    have hre : (⟪T f, f⟫).re = (⟪f, T f⟫).re := inner_re_symm (𝕜 := ℂ) (T f) f
    change |(⟪T f, f⟫).re / ‖f‖^2| ≤ C
    have hnon : 0 ≤ (⟪T f, f⟫).re := hT.re_inner_nonneg_left f
    rw [abs_of_nonneg (div_nonneg hnon (sq_nonneg _)), hre]
    by_cases hf : f = 0
    · simpa [hf] using hC
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (h f)

lemma positive_exists_form_gt (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ}
    (hC : 0 ≤ C) (h : C < ‖T‖) : ∃ f, C * ‖f‖^2 < (⟪f, T f⟫).re := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) ((positive_norm_le_iff T hT hC).mpr hn)

end PositiveNorm

section Compressed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def compressedHeat (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  mask D hD ∘L heat w hw hn ∘L mask D hD

lemma heat_positive (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (heat w hw hn).IsPositive := spectralOp_positive _ _ _ (fun _ => (Real.exp_pos _).le)

lemma compressedHeat_positive (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (compressedHeat D hD w hw hn).IsPositive := by
  have hp := (heat_positive w hw hn).adjoint_conj (mask D hD)
  rwa [mask_adjoint] at hp

lemma compressedHeat_inner (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, compressedHeat D hD w hw hn f⟫).re =
      ‖mask D hD f‖^2 - energy w (mask D hD f) := by
  change (⟪f, mask D hD (heat w hw hn (mask D hD f))⟫).re = _
  rw [← mask_inner, heat_inner]

lemma compressedHeat_norm_le_one (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    ‖compressedHeat D hD w hw hn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖mask D hD (heat w hw hn (mask D hD f))‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact (mask_norm_le _ _ _).trans ((spectralOp_norm_le _ _ _ _).trans (mask_norm_le _ _ _))

end Compressed
end HeatL2

namespace HeatL2
section Average
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma integrable_translate (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : Integrable (fun z => translate (A z) f) ν := by
  apply Integrable.mono' (integrable_const ‖f‖)
    ((translate_continuous f).comp A.continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => (translate (A z)).norm_map f |>.le

omit [FiniteDimensional ℝ F] [BorelSpace F] in
lemma average_norm_le (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : ‖∫ z, translate (A z) f ∂ν‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun z => (translate (A z)).norm_map f |>.le :
      ∀ᵐ z ∂ν, ‖translate (A z) f‖ ≤ ‖f‖)

noncomputable def averageLinear (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν] :
    Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) where
  toFun f := ∫ z, translate (A z) f ∂ν
  map_add' f g := by
    simp only [map_add]
    exact integral_add (integrable_translate A ν f) (integrable_translate A ν g)
  map_smul' c f := by simp only [map_smul, integral_smul, RingHom.id_apply]

noncomputable def average (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν] :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (averageLinear A ν).mkContinuous 1 (fun f => by change ‖∫ z, translate (A z) f ∂ν‖ ≤ 1 * ‖f‖; simpa using average_norm_le A ν f)

lemma average_apply (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : average A ν f = ∫ z, translate (A z) f ∂ν := rfl

lemma inner_average (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ ξ, (∫ z, phase (A z) ξ ∂ν) * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  have hp : Integrable (fun ξ => (𝓕 f) ξ * conj ((𝓕 g) ξ)) (volume : Measure E) := by
    simpa only [RCLike.inner_apply] using L2.integrable_inner (𝕜 := ℂ) (𝓕 g) (𝓕 f)
  have hm : Continuous (fun p : F × E => phase (A p.1) p.2) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((A.continuous.comp continuous_fst).inner continuous_snd)
  have hi : Integrable (fun p : F × E => phase (A p.1) p.2 *
      ((𝓕 f) p.2 * conj ((𝓕 g) p.2))) (ν.prod volume) := by
    apply Integrable.mono' (hp.norm.comp_snd ν) (hm.aestronglyMeasurable.mul hp.aestronglyMeasurable.comp_snd)
    exact Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply, norm_mul, phase_norm, one_mul, le_refl]
  have hinner (z : F) : ⟪g, translate (A z) f⟫ =
      ∫ ξ, phase (A z) ξ * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
    rw [← Lp.inner_fourier_eq, fourier_translate]
    exact inner_mulOp _ _ _ _ _
  simp_rw [hinner]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => integral_mul_const _ _

noncomputable def gaussianSymbol (A : F →L[ℝ] E) (ξ : E) : ℝ :=
  ‖(2*Real.pi) • A.adjoint ξ‖^2 / 2

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gaussianSymbol_nonneg (A : F →L[ℝ] E) (ξ : E) : 0 ≤ gaussianSymbol A ξ := by
  unfold gaussianSymbol
  positivity

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gaussianSymbol_continuous (A : F →L[ℝ] E) : Continuous (gaussianSymbol A) := by
  unfold gaussianSymbol
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma integral_phase_gaussian (A : F →L[ℝ] E) (ξ : E) :
    (∫ z, phase (A z) ξ ∂ProbabilityTheory.stdGaussian F) =
      (Real.exp (-gaussianSymbol A ξ) : ℂ) := by
  have he := ProbabilityTheory.charFun_stdGaussian ((2*Real.pi) • A.adjoint ξ)
  rw [charFun_apply] at he
  have hf : (fun z => phase (A z) ξ) = fun z =>
      Complex.exp ((inner ℝ z ((2*Real.pi) • A.adjoint ξ) : ℂ) * Complex.I) := by
    ext z
    rw [phase, Real.fourierChar_apply, inner_smul_right, A.adjoint_inner_right]
  rw [hf, he, gaussianSymbol, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma average_gaussian_eq_heat (A : F →L[ℝ] E) :
    average A (ProbabilityTheory.stdGaussian F) =
      heat (gaussianSymbol A) (gaussianSymbol_continuous A).aestronglyMeasurable
        (gaussianSymbol_nonneg A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [inner_average]
  simp_rw [integral_phase_gaussian]
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  apply integral_congr_ae
  have hb : ∀ ξ, |Real.exp (-gaussianSymbol A ξ)| ≤ 1 := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (gaussianSymbol_nonneg A ξ))
  filter_upwards [spectralOp_fourier (fun ξ => Real.exp (-gaussianSymbol A ξ))
    (Real.continuous_exp.comp_aestronglyMeasurable (gaussianSymbol_continuous A).aestronglyMeasurable.neg)
    hb f] with ξ hξ
  change _ = inner ℂ ((𝓕 g) ξ) ((𝓕 (heat _ _ _ f)) ξ)
  rw [heat, hξ]
  simp only [RCLike.inner_apply]
  ring

end Average
end HeatL2

namespace HeatL2
section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_energy (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun ξ => loss (w ξ) * ‖(𝓕 f) ξ‖^2) := by
  apply integrable_weight (fun ξ => loss (w ξ))
    (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
    (C := 1) _ (𝓕 f)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [abs_of_nonneg (loss_nonneg (hn ξ))]
    exact loss_le_one _

lemma energy_le_norm_sq (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) : energy w f ≤ ‖f‖^2 := by
  rw [← Lp.norm_fourier_eq f, norm_sq_integral]
  apply integral_mono (integrable_energy w hw hn f)
    ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
  intro ξ
  exact mul_le_of_le_one_left (sq_nonneg _) (loss_le_one _)

lemma energy_comparison {w v : E → ℝ} (hw : AEStronglyMeasurable w volume)
    (hv : AEStronglyMeasurable v volume) (hwn : ∀ x, 0 ≤ w x) (hvn : ∀ x, 0 ≤ v x)
    {C : ℝ} (h : ∀ ξ, loss (w ξ) ≤ C * loss (v ξ)) (f : Lp ℂ 2 (volume : Measure E)) :
    energy w f ≤ C * energy v f := by
  rw [energy, energy, ← integral_const_mul]
  apply integral_mono (integrable_energy w hw hwn f) ((integrable_energy v hv hvn f).const_mul C)
  intro ξ
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h ξ) (sq_nonneg ‖(𝓕 f) ξ‖)

lemma energy_mean_ge {ι : Type*} (s : Finset ι) (q : ι → ℝ) (w : ι → E → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i = 1)
    (hw : ∀ i ∈ s, AEStronglyMeasurable (w i) volume)
    (hn : ∀ i ∈ s, ∀ ξ, 0 ≤ w i ξ) (f : Lp ℂ 2 (volume : Measure E)) :
    ∑ i ∈ s, q i * energy (w i) f ≤ energy (fun ξ => ∑ i ∈ s, q i * w i ξ) f := by
  have hi i (h : i ∈ s) := (integrable_energy (w i) (hw i h) (hn i h) f).const_mul (q i)
  have hw' : AEStronglyMeasurable (fun ξ => ∑ i ∈ s, q i * w i ξ) volume := by
    exact s.aestronglyMeasurable_fun_sum fun i hi => (hw i hi).const_mul (q i)
  have hn' ξ : 0 ≤ ∑ i ∈ s, q i * w i ξ := Finset.sum_nonneg fun i hi => mul_nonneg (hq i hi) (hn i hi ξ)
  have he : (∑ i ∈ s, q i * energy (w i) f) = ∫ ξ, ∑ i ∈ s, q i * (loss (w i ξ) * ‖(𝓕 f) ξ‖^2) := by
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  rw [he]
  apply integral_mono (integrable_finsetSum s hi) (integrable_energy _ hw' hn' f)
  intro ξ
  simpa only [← mul_assoc, ← Finset.sum_mul] using
    mul_le_mul_of_nonneg_right (loss_mean_ge s q (fun i => w i ξ) hq hs) (sq_nonneg ‖(𝓕 f) ξ‖)

noncomputable def directionalSymbol (e : E) (ξ : E) : ℝ := (2*Real.pi*inner ℝ e ξ)^2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma directionalSymbol_nonneg (e ξ : E) : 0 ≤ directionalSymbol e ξ := sq_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma directionalSymbol_continuous (e : E) : Continuous (directionalSymbol e) := by
  unfold directionalSymbol
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_one_sq_le (e ξ : E) (h : ℝ) :
    ‖phase (h • e) ξ - 1‖^2 ≤ h^2 * directionalSymbol e ξ := by
  have hb : ‖phase (h • e) ξ - 1‖ ≤ ‖2*Real.pi*inner ℝ (h • e) ξ‖ := by
    rw [phase, Real.fourierChar_apply, mul_comm _ Complex.I]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb
  have he : ‖2*Real.pi*inner ℝ (h • e) ξ‖^2 = h^2 * directionalSymbol e ξ := by
    simp only [inner_smul_left, starRingEnd_apply, star_trivial,
      Real.norm_eq_abs, sq_abs, directionalSymbol]
    ring
  exact hs.trans_eq he

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_one_sq_le_four (a ξ : E) : ‖phase a ξ - 1‖^2 ≤ 4 := by
  have hn : ‖phase a ξ - 1‖ ≤ 2 := by
    simpa only [phase_norm, norm_one, one_add_one_eq_two] using norm_sub_le (phase a ξ) (1:ℂ)
  nlinarith [norm_nonneg (phase a ξ - 1)]

lemma directional_translate_bound (e : E) (h η : ℝ) (hη : 0 < η)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate (h • e) f - f‖^2 ≤ (h^2 + 4*η)/η * energy (fun ξ => η * directionalSymbol e ξ) f := by
  rw [translate_sub_norm_sq, energy, ← integral_const_mul]
  have hw : AEStronglyMeasurable (fun ξ => η * directionalSymbol e ξ) volume :=
    ((directionalSymbol_continuous e).const_mul η).aestronglyMeasurable
  have hn ξ := mul_nonneg hη.le (directionalSymbol_nonneg e ξ)
  have hleft : Integrable (fun ξ => ‖phase (h • e) ξ - 1‖^2 * ‖(𝓕 f) ξ‖^2) := by
    apply integrable_weight (fun ξ => ‖phase (h • e) ξ - 1‖^2)
      (((phase_continuous _).sub continuous_const).norm.pow 2).aestronglyMeasurable
      (C := 4) _ (𝓕 f)
    exact Filter.Eventually.of_forall fun ξ => by
      simpa only [abs_pow, abs_norm] using phase_sub_one_sq_le_four (h • e) ξ
  apply integral_mono hleft ((integrable_energy _ hw hn f).const_mul _)
  intro ξ
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (bound_by_loss (sq_nonneg h) hη (directionalSymbol_nonneg e ξ)
      (phase_sub_one_sq_le e ξ h) (phase_sub_one_sq_le_four (h • e) ξ)) (sq_nonneg ‖(𝓕 f) ξ‖)

end Energy
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

lemma sqrt_pair_sub_sq_le (a b c d : ℝ) :
    (Real.sqrt (a^2+b^2) - Real.sqrt (c^2+d^2))^2 ≤ (a-c)^2+(b-d)^2 := by
  have hx : 0 ≤ a^2+b^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy : 0 ≤ c^2+d^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : (a*c+b*d)^2 ≤ (a^2+b^2)*(c^2+d^2) := by
    nlinarith [sq_nonneg (a*d-b*c)]
  have hp : (a^2+b^2)*(c^2+d^2) =
      (Real.sqrt (a^2+b^2)*Real.sqrt (c^2+d^2))^2 := by
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hcs : a*c+b*d ≤ Real.sqrt (a^2+b^2)*Real.sqrt (c^2+d^2) := by
    rw [hp] at hs
    nlinarith [mul_nonneg (Real.sqrt_nonneg (a^2+b^2)) (Real.sqrt_nonneg (c^2+d^2))]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma sqrt_mix_sub_sq_le (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (a b c d : ℝ) :
    (Real.sqrt (t*a^2+u*b^2) - Real.sqrt (t*c^2+u*d^2))^2 ≤ t*(a-c)^2+u*(b-d)^2 := by
  have he (x y : ℝ) : (Real.sqrt t*x)^2+(Real.sqrt u*y)^2=t*x^2+u*y^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hu]
  have h := sqrt_pair_sub_sq_le (Real.sqrt t*a) (Real.sqrt u*b) (Real.sqrt t*c) (Real.sqrt u*d)
  rw [he, he] at h
  have hr : (Real.sqrt t*a-Real.sqrt t*c)^2+(Real.sqrt u*b-Real.sqrt u*d)^2=
      t*(a-c)^2+u*(b-d)^2 := by
    rw [← mul_sub, ← mul_sub, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hu]
  exact h.trans_eq hr

lemma sqrt_mix_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (t*a^2+u*b^2) ≤ Real.sqrt t*a+Real.sqrt u*b := by
  have hr : 0 ≤ Real.sqrt t*a+Real.sqrt u*b := by positivity
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hr, ?_⟩
  have h₁ := Real.sq_sqrt ht
  have h₂ := Real.sq_sqrt hu
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg t) ha) (mul_nonneg (Real.sqrt_nonneg u) hb)]

section Mixture
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

noncomputable def mixFun (t : ℝ) (f g : Lp ℂ 2 μ) (x : X) : ℂ :=
  (Real.sqrt (t*‖f x‖^2+(1-t)*‖g x‖^2) : ℝ)

lemma mixFun_memLp (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    MemLp (mixFun t f g) 2 μ := by
  have hu := sub_nonneg.mpr ht'
  have hmeas : AEStronglyMeasurable (mixFun t f g) μ := by
    unfold mixFun
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable
      ((((Lp.memLp f).aestronglyMeasurable.norm.pow 2).const_mul t).add
      (((Lp.memLp g).aestronglyMeasurable.norm.pow 2).const_mul (1-t))))
  apply MemLp.of_le ((Lp.memLp f).norm.const_mul (Real.sqrt t) |>.add
    ((Lp.memLp g).norm.const_mul (Real.sqrt (1-t)))) hmeas
  exact Filter.Eventually.of_forall fun x => by
    rw [mixFun, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change _ ≤ ‖Real.sqrt t * ‖f x‖ + Real.sqrt (1-t) * ‖g x‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sqrt_mix_bound t (1-t) ht hu _ _ (norm_nonneg _) (norm_nonneg _)

noncomputable def mixture (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (mixFun_memLp t ht ht' f g).toLp (mixFun t f g)

lemma mixture_coe (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    (mixture t ht ht' f g : X → ℂ) =ᵐ[μ] mixFun t f g := MemLp.coeFn_toLp _

lemma mixFun_norm_sq (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) (x : X) :
    ‖mixFun t f g x‖^2 = t*‖f x‖^2+(1-t)*‖g x‖^2 := by
  rw [mixFun, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt]
  positivity

lemma mixture_norm_sq (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    ‖mixture t ht ht' f g‖^2 = t*‖f‖^2+(1-t)*‖g‖^2 := by
  rw [norm_sq_integral, norm_sq_integral f, norm_sq_integral g]
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hg := (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul t) (hg.const_mul (1-t))]
  apply integral_congr_ae
  filter_upwards [mixture_coe t ht ht' f g] with x hx
  rw [hx, mixFun_norm_sq t ht ht']

lemma mixFun_sub_sq_le (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) (x y : X) :
    ‖mixFun t f g x - mixFun t f g y‖^2 ≤ t*‖f x-f y‖^2+(1-t)*‖g x-g y‖^2 := by
  have hu := sub_nonneg.mpr ht'
  have hb := sqrt_mix_sub_sq_le t (1-t) ht hu ‖f x‖ ‖g x‖ ‖f y‖ ‖g y‖
  have h₁ : (‖f x‖-‖f y‖)^2 ≤ ‖f x-f y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.mpr (abs_norm_sub_norm_le (f x) (f y)))
  have h₂ : (‖g x‖-‖g y‖)^2 ≤ ‖g x-g y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.mpr (abs_norm_sub_norm_le (g x) (g y)))
  have h := hb.trans (add_le_add (mul_le_mul_of_nonneg_left h₁ ht) (mul_le_mul_of_nonneg_left h₂ hu))
  simpa only [mixFun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

lemma mixture_supported (D : Set X) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 μ) (hf : f ∈ supported D) (hg : g ∈ supported D) :
    mixture t ht ht' f g ∈ supported D := by
  change ∀ᵐ x ∂μ, x ∉ D → mixture t ht ht' f g x = 0
  filter_upwards [mixture_coe t ht ht' f g, hf, hg] with x hx hf hg hnot
  simp only [hx, mixFun, hf hnot, hg hnot, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Real.sqrt_zero, Complex.ofReal_zero]

end Mixture

section MixtureTranslation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma mixture_translation_sq_le (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure E)) (a : E) :
    ‖translate a (mixture t ht ht' f g) - mixture t ht ht' f g‖^2 ≤
      t * ‖translate a f - f‖^2 + (1-t) * ‖translate a g - g‖^2 := by
  rw [norm_sq_integral, norm_sq_integral (translate a f - f), norm_sq_integral (translate a g - g)]
  have hf := (Lp.memLp (translate a f - f)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hg := (Lp.memLp (translate a g - g)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul t) (hg.const_mul (1-t))]
  apply integral_mono_ae
    ((Lp.memLp _).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((hf.const_mul t).add (hg.const_mul (1-t)))
  have hm := mixture_coe t ht ht' f g
  have hma := (measurePreserving_add_right (volume : Measure E) a).quasiMeasurePreserving.ae_eq_comp hm
  filter_upwards [hm, hma, translate_coe a (mixture t ht ht' f g), translate_coe a f,
    translate_coe a g, Lp.coeFn_sub (translate a (mixture t ht ht' f g)) (mixture t ht ht' f g),
    Lp.coeFn_sub (translate a f) f, Lp.coeFn_sub (translate a g) g] with x hm hma hb hf hg hc hd he
  simp only [Pi.sub_apply] at hc hd he
  change mixture t ht ht' f g (x+a) = mixFun t f g (x+a) at hma
  simp only [Pi.add_apply]
  rw [hc, hb, hma, hm, hd, he, hf, hg]
  exact mixFun_sub_sq_le t ht ht' f g (x+a) x

end MixtureTranslation
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2
section Difference
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in
lemma integrable_difference_sq (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun z => ‖translate (A z) f - f‖^2) ν := by
  apply Integrable.mono' (integrable_const (4 * ‖f‖^2))
    ((((translate_continuous f).comp A.continuous).sub continuous_const).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_sub_le (translate (A z) f) f
    rw [(translate (A z)).norm_map] at h
    change ‖translate (A z) f - f‖^2 ≤ 4 * ‖f‖^2
    nlinarith [norm_nonneg (translate (A z) f - f)]

lemma average_difference_sq (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) :
    (∫ z, ‖translate (A z) f - f‖^2 ∂ν) = 2 * (‖f‖^2 - (⟪f, average A ν f⟫).re) := by
  have hi : Integrable (fun z => (⟪f, translate (A z) f⟫).re) ν :=
    ((integrable_translate A ν f).const_inner (𝕜 := ℂ) f).re
  have he z : ‖translate (A z) f - f‖^2 =
      ‖f‖^2 - 2 * (⟪f, translate (A z) f⟫).re + ‖f‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ), (translate (A z)).norm_map, inner_re_symm (𝕜 := ℂ)]
    rfl
  simp_rw [he]
  have hi' : Integrable (fun z => ‖f‖^2 - 2 * (⟪f, translate (A z) f⟫).re) ν :=
    (integrable_const (‖f‖^2)).sub (hi.const_mul 2)
  have hr := integral_re ((integrable_translate A ν f).const_inner (𝕜 := ℂ) f)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [integral_add hi' (integrable_const (‖f‖^2)),
    integral_sub (integrable_const (‖f‖^2)) (hi.const_mul 2), integral_const_mul,
    integral_const, probReal_univ, one_smul, hr,
    integral_inner (integrable_translate A ν f), ← average_apply]
  ring

lemma gaussian_energy_difference (A : F →L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    energy (gaussianSymbol A) f = (1/2:ℝ) *
      ∫ z, ‖translate (A z) f - f‖^2 ∂ProbabilityTheory.stdGaussian F := by
  rw [average_difference_sq, average_gaussian_eq_heat, heat_inner]
  ring

end Difference
end HeatL2

lemma selfAdjoint_norm_pow {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (a : A) (ha : IsSelfAdjoint a) (n : ℕ) (hn : n ≠ 0) : ‖a^n‖ = ‖a‖^n := by
  by_cases hz : a = 0
  · simp [hz, zero_pow hn]
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hlarge : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self (n := n))
  have hrem : 2^n-n ≠ 0 := Nat.ne_zero_of_lt (Nat.sub_pos_of_lt (Nat.lt_two_pow_self (n := n)))
  have he : n + (2^n-n) = 2^n := Nat.add_sub_of_le hlarge
  have h : ‖a‖^n * ‖a‖^(2^n-n) ≤ ‖a^n‖ * ‖a‖^(2^n-n) := by
    calc
      _ = ‖a‖^(2^n) := by rw [← pow_add, he]
      _ = ‖a^(2^n)‖ := (ha.norm_pow_two_pow n).symm
      _ = ‖a^n * a^(2^n-n)‖ := by rw [← pow_add, he]
      _ ≤ ‖a^n‖ * ‖a^(2^n-n)‖ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pow_le' _ (Nat.pos_of_ne_zero hrem)) (norm_nonneg _)
  exact le_antisymm (norm_pow_le' _ (Nat.pos_of_ne_zero hn)) ((mul_le_mul_iff_left₀ (pow_pos hp _)).mp h)

open MeasureTheory Filter ComplexConjugate
open scoped ComplexInnerProductSpace ENNReal

namespace HeatL2
section Absolute
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma abs_memLp (f : Lp ℂ 2 μ) : MemLp (fun x => (‖f x‖ : ℂ)) 2 μ := by
  apply MemLp.of_le (Lp.memLp f)
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable.norm)
  exact Filter.Eventually.of_forall fun x => by simp

noncomputable def absolute (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (abs_memLp f).toLp (fun x => (‖f x‖ : ℂ))

lemma absolute_coe (f : Lp ℂ 2 μ) : (absolute f : X → ℂ) =ᵐ[μ] fun x => (‖f x‖ : ℂ) :=
  MemLp.coeFn_toLp _

lemma absolute_norm (f : Lp ℂ 2 μ) : ‖absolute f‖ = ‖f‖ := by
  have he : ∀ᵐ x ∂μ, ‖absolute f x‖ = ‖f x‖ := by
    filter_upwards [absolute_coe f] with x hx
    simp [hx]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))

variable [IsFiniteMeasure μ]

noncomputable def oneLp : Lp ℂ 2 μ := Lp.const 2 μ 1

lemma oneLp_coe : ((oneLp : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun _ => 1 := Lp.coeFn_const 2 μ 1

lemma integral_norm_le (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖ := by
  have he : ⟪(oneLp : Lp ℂ 2 μ), absolute f⟫ = (∫ x, ‖f x‖ ∂μ : ℝ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [oneLp_coe (μ := μ), absolute_coe f] with x h₁ h₂
    simp only [h₁, h₂, RCLike.inner_apply, map_one, mul_one]
  calc
    _ = (⟪(oneLp : Lp ℂ 2 μ), absolute f⟫).re := by rw [he]; rfl
    _ ≤ ‖⟪(oneLp : Lp ℂ 2 μ), absolute f⟫‖ := Complex.re_le_norm _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖absolute f‖ := norm_inner_le_norm _ _
    _ = _ := by rw [absolute_norm]

end Absolute

structure BoundedKernel (X : Type*) [MeasurableSpace X] where
  value : X × X → ℝ
  measurable : Measurable value
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  nonneg : ∀ p, 0 ≤ value p
  le_bound : ∀ p, value p ≤ bound

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

noncomputable def kernelFun (f : Lp ℂ 2 μ) (x : X) : ℂ :=
  ∫ y, (k.value (x,y) : ℂ) * f y ∂μ

lemma kernel_section_integrable (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun y => (k.value (x,y) : ℂ) * f y) μ := by
  apply Integrable.mono' (((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞)≤2)).norm.const_mul k.bound)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (k.measurable.comp measurable_prodMk_left).aestronglyMeasurable).mul (Lp.memLp f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖(k.value (x,y) : ℂ) * f y‖ ≤ k.bound * ‖f y‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _)]
    exact mul_le_mul_of_nonneg_right (k.le_bound _) (norm_nonneg _)

lemma kernelFun_bound (f : Lp ℂ 2 μ) (x : X) :
    ‖kernelFun k f x‖ ≤ k.bound * ∫ y, ‖f y‖ ∂μ := by
  unfold kernelFun
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (kernel_section_integrable k f x).norm
    (((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞)≤2)).norm.const_mul k.bound)
  intro y
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _)]
  exact mul_le_mul_of_nonneg_right (k.le_bound _) (norm_nonneg _)

lemma kernelFun_norm_bound (f : Lp ℂ 2 μ) (x : X) :
    ‖kernelFun k f x‖ ≤ k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖ := by
  exact (kernelFun_bound k f x).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (integral_norm_le f) k.bound_nonneg)

lemma kernelFun_memLp (f : Lp ℂ 2 μ) : MemLp (kernelFun k f) 2 μ := by
  have hm : AEStronglyMeasurable (fun p : X × X => (k.value p : ℂ) * f p.2) (μ.prod μ) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable k.measurable.aestronglyMeasurable).mul
      (Lp.memLp f).aestronglyMeasurable.comp_snd
  apply MemLp.of_bound hm.integral_prod_right' (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖)
  exact Filter.Eventually.of_forall (kernelFun_norm_bound k f)

noncomputable def kernelLp (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (kernelFun_memLp k f).toLp (kernelFun k f)

lemma kernelLp_coe (f : Lp ℂ 2 μ) : (kernelLp k f : X → ℂ) =ᵐ[μ] kernelFun k f :=
  MemLp.coeFn_toLp _

lemma kernelLp_add (f g : Lp ℂ 2 μ) : kernelLp k (f+g) = kernelLp k f+kernelLp k g := by
  apply Lp.ext
  filter_upwards [kernelLp_coe k (f+g), kernelLp_coe k f, kernelLp_coe k g,
    Lp.coeFn_add (kernelLp k f) (kernelLp k g)] with x h₁ h₂ h₃ h₄
  simp only [Pi.add_apply] at h₄
  rw [h₁, h₄, h₂, h₃]
  unfold kernelFun
  rw [← integral_add (kernel_section_integrable k f x) (kernel_section_integrable k g x)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with y hy
  simp only [hy, Pi.add_apply, mul_add]

lemma kernelLp_smul (c : ℂ) (f : Lp ℂ 2 μ) : kernelLp k (c • f) = c • kernelLp k f := by
  apply Lp.ext
  filter_upwards [kernelLp_coe k (c • f), kernelLp_coe k f, Lp.coeFn_smul c (kernelLp k f)] with x h₁ h₂ h₃
  simp only [Pi.smul_apply, smul_eq_mul] at h₃
  rw [h₁, h₃, h₂]
  unfold kernelFun
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with y hy
  simp only [hy, Pi.smul_apply, smul_eq_mul]
  ring

lemma kernelLp_norm_le (f : Lp ℂ 2 μ) :
    ‖kernelLp k f‖ ≤ (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖^2) * ‖f‖ := by
  have h : ‖kernelLp k f‖ ≤ (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖) * ‖(oneLp : Lp ℂ 2 μ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [kernelLp_coe k f, oneLp_coe (μ := μ)] with x h₁ h₂
    rw [h₁, h₂, norm_one, mul_one]
    exact kernelFun_norm_bound k f x
  nlinarith [h]

noncomputable def kernelLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := kernelLp k
  map_add' := kernelLp_add k
  map_smul' c f := by simpa only [RingHom.id_apply] using kernelLp_smul k c f

noncomputable def kernelOp : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (kernelLinear k).mkContinuous (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖^2) (kernelLp_norm_le k)

lemma kernelOp_coe (f : Lp ℂ 2 μ) : (kernelOp k f : X → ℂ) =ᵐ[μ] kernelFun k f := kernelLp_coe k f

lemma inner_one_eq_integral (f : Lp ℂ 2 μ) :
    ⟪(oneLp : Lp ℂ 2 μ), f⟫ = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneLp_coe (μ := μ)] with x hx
  simp only [hx, RCLike.inner_apply, map_one, mul_one]

lemma kernelFun_domination (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) (x : X) :
    ‖kernelFun k f x‖ ≤ (kernelFun k g x).re := by
  unfold kernelFun
  have hr := integral_re (kernel_section_integrable k g x)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [← hr]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (kernel_section_integrable k f x).norm
    (kernel_section_integrable k g x).re
  filter_upwards [hfg] with y hy
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (k.nonneg _), RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hy (k.nonneg _)

lemma kernelOp_domination (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) :
    ∀ᵐ x ∂μ, ‖kernelOp k f x‖ ≤ (kernelOp k g x).re := by
  filter_upwards [kernelOp_coe k f, kernelOp_coe k g] with x hf hg
  rw [hf, hg]
  exact kernelFun_domination k f g hfg x

lemma kernel_pow_domination (n : ℕ) (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) :
    ∀ᵐ x ∂μ, ‖(kernelOp k ^ n) f x‖ ≤ ((kernelOp k ^ n) g x).re := by
  induction n with
  | zero => simpa using hfg
  | succ n hn =>
    simpa only [pow_succ', mul_apply_eq_comp] using kernelOp_domination k _ _ hn

lemma kernel_norm_le_integral (f : Lp ℂ 2 μ) :
    ‖kernelOp k f‖ ≤ k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * (∫ x, ‖f x‖ ∂μ) := by
  have h : ‖kernelOp k f‖ ≤ (k.bound * ∫ x, ‖f x‖ ∂μ) * ‖(oneLp : Lp ℂ 2 μ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [kernelOp_coe k f, oneLp_coe (μ := μ)] with x hx ho
    rw [hx, ho, norm_one, mul_one]
    exact kernelFun_bound k f x
  nlinarith [h]

noncomputable def pathMass (n : ℕ) : ℝ :=
  (⟪(oneLp : Lp ℂ 2 μ), (kernelOp k ^ n) oneLp⟫).re

lemma pathMass_eq_integral (n : ℕ) :
    pathMass (μ := μ) k n = ∫ x, (((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ)) x).re ∂μ := by
  rw [pathMass, inner_one_eq_integral]
  have hr := integral_re ((Lp.memLp ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))).integrable (by norm_num))
  simpa only [RCLike.re_eq_complex_re] using hr.symm

lemma pathMass_nonneg (n : ℕ) : 0 ≤ pathMass (μ := μ) k n := by
  rw [pathMass_eq_integral]
  apply integral_nonneg_of_ae
  have h : ∀ᵐ x ∂μ, ‖(0 : Lp ℂ 2 μ) x‖ ≤ ((oneLp : Lp ℂ 2 μ) x).re := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ, oneLp_coe (μ := μ)] with x hz ho
    simp only [Pi.zero_apply] at hz
    rw [hz, ho]
    norm_num
  have hd := kernel_pow_domination k n 0 oneLp h
  simp only [map_zero] at hd
  filter_upwards [hd, Lp.coeFn_zero ℂ 2 μ] with x hx hz
  simp only [Pi.zero_apply] at hz
  rwa [hz, norm_zero] at hx

lemma pathMass_le (n : ℕ) :
    pathMass (μ := μ) k n ≤ ‖(oneLp : Lp ℂ 2 μ)‖^2 * ‖(kernelOp (μ := μ) k)‖^n := by
  unfold pathMass
  calc
    _ ≤ ‖⟪(oneLp : Lp ℂ 2 μ), (kernelOp k ^ n) oneLp⟫‖ := Complex.re_le_norm _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖(kernelOp k ^ n) oneLp‖ := norm_inner_le_norm _ _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp k ^ n : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ * ‖(oneLp : Lp ℂ 2 μ)‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp (μ := μ) k)‖^n * ‖(oneLp : Lp ℂ 2 μ)‖) := by
      gcongr
      rcases n with _ | n
      · exact ContinuousLinearMap.norm_id_le
      · exact norm_pow_le' _ (Nat.succ_pos _)
    _ = _ := by ring

lemma kernel_pow_norm_le_pathMass (n : ℕ) :
    ‖(kernelOp (μ := μ) k ^ (n+2))‖ ≤
      k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2 * pathMass (μ := μ) k n := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pathMass_nonneg k n)
  intro f
  let C := k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖
  have hf : ∀ᵐ x ∂μ, ‖kernelOp k f x‖ ≤ (((C : ℂ) • (oneLp : Lp ℂ 2 μ)) x).re := by
    filter_upwards [kernelOp_coe k f, oneLp_coe (μ := μ),
      Lp.coeFn_smul (C : ℂ) (oneLp : Lp ℂ 2 μ)] with x hx ho hs
    rw [hx, hs]
    simp only [Pi.smul_apply, smul_eq_mul, ho, mul_one, Complex.ofReal_re]
    exact kernelFun_norm_bound k f x
  have hd := kernel_pow_domination k n _ _ hf
  rw [map_smul] at hd
  have hi : (∫ x, ‖(kernelOp k ^ n) (kernelOp k f) x‖ ∂μ) ≤
      C * pathMass (μ := μ) k n := by
    rw [pathMass_eq_integral, ← integral_const_mul]
    have hrg : Integrable (fun x => (((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ)) x).re) μ := by
      simpa only [RCLike.re_eq_complex_re] using
        ((Lp.memLp ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))).integrable (by norm_num)).re
    apply integral_mono_ae ((Lp.memLp ((kernelOp k ^ n) (kernelOp k f))).integrable (by norm_num)).norm
      (hrg.const_mul C)
    filter_upwards [hd, Lp.coeFn_smul (C : ℂ) ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))] with x hx hs
    rw [hs] at hx
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hx
  have he : (kernelOp k ^ (n+2)) f = kernelOp k ((kernelOp k ^ n) (kernelOp k f)) := by
    rw [show n+2 = (n+1)+1 by omega, pow_succ', pow_succ,
      mul_apply_eq_comp, mul_apply_eq_comp]
  rw [he]
  apply (kernel_norm_le_integral k _).trans
  apply (mul_le_mul_of_nonneg_left hi (mul_nonneg k.bound_nonneg (norm_nonneg _))).trans
  exact le_of_eq (by dsimp [C]; ring)

lemma kernel_pair_integrable (f g : Lp ℂ 2 μ) :
    Integrable (fun p : X × X => (k.value p : ℂ) * g p.2 * conj (f p.1)) (μ.prod μ) := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
  have hg := ((Lp.memLp g).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
  apply Integrable.mono' ((hf.mul_prod hg).const_mul k.bound)
    (((Complex.continuous_ofReal.comp_aestronglyMeasurable k.measurable.aestronglyMeasurable).mul
      (Lp.memLp g).aestronglyMeasurable.comp_snd).mul
        (continuous_star.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable.comp_fst))
  exact Filter.Eventually.of_forall fun p => by
    change ‖(k.value p : ℂ) * g p.2 * conj (f p.1)‖ ≤ k.bound * (‖f p.1‖ * ‖g p.2‖)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _), Complex.norm_conj]
    calc
      _ ≤ k.bound * ‖g p.2‖ * ‖f p.1‖ := by gcongr; exact k.le_bound p
      _ = _ := by ring

lemma inner_kernel (f g : Lp ℂ 2 μ) :
    ⟪f, kernelOp k g⟫ = ∫ x, ∫ y, (k.value (x,y) : ℂ) * g y * conj (f x) ∂μ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelOp_coe k g] with x hx
  simp only [RCLike.inner_apply, hx, kernelFun, integral_mul_const]

lemma kernelOp_selfAdjoint (hs : ∀ x y, k.value (x,y) = k.value (y,x)) :
    IsSelfAdjoint (kernelOp (μ := μ) k) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪kernelOp k f, g⟫ = ⟪f, kernelOp k g⟫
  rw [← inner_conj_symm, inner_kernel, ← integral_conj]
  simp_rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  conv_rhs => rw [inner_kernel, integral_integral_swap (kernel_pair_integrable k f g)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun y => by dsimp only; rw [hs x y]; ring)

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace

namespace HeatL2

lemma le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^n ≤ C*b^n) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have ha' : 0 < a := hb.trans_lt hab
  have hr : b/a < 1 := (div_lt_one ha').mpr hab
  have ht : Tendsto (fun n : ℕ => C*(b/a)^n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb ha) hr)
  have hh (n : ℕ) : 1 ≤ C*(b/a)^n := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos ha' n)]
    simpa only [one_mul] using h n
  have := ge_of_tendsto' ht hh
  linarith

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

lemma kernel_norm_pow_le_pathMass (hs : ∀ x y, k.value (x,y) = k.value (y,x)) (n : ℕ) :
    ‖kernelOp (μ := μ) k‖^(n+2) ≤
      k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2 * pathMass (μ := μ) k n := by
  rw [← selfAdjoint_norm_pow _ (kernelOp_selfAdjoint k hs) (n+2) (by omega)]
  exact kernel_pow_norm_le_pathMass k n

lemma norm_lower_of_pathMass_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : ∀ n : ℕ, c*a^n ≤ pathMass (μ := μ) k n) : a ≤ ‖kernelOp (μ := μ) k‖ := by
  apply le_of_pow_le_const_mul_pow ha (norm_nonneg _) (C := ‖(oneLp : Lp ℂ 2 μ)‖^2/c)
  intro n
  have hn := (h n).trans (pathMass_le k n)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using hn

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ComplexInnerProductSpace ENNReal
namespace HeatL2
section Restrict
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (D : Set X) (hD : MeasurableSet D)
noncomputable def extendLp (f : Lp ℂ 2 (μ.restrict D)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)
lemma extendLp_coe (f : Lp ℂ 2 (μ.restrict D)) :
    (extendLp D hD f : X → ℂ) =ᵐ[μ] D.indicator f := MemLp.coeFn_toLp _
lemma extendLp_norm (f : Lp ℂ 2 (μ.restrict D)) : ‖extendLp D hD f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (extendLp_coe D hD f), eLpNorm_indicator_eq_eLpNorm_restrict hD]
lemma extendLp_supported (f : Lp ℂ 2 (μ.restrict D)) : extendLp D hD f ∈ supported D := by
  filter_upwards [extendLp_coe D hD f] with x hx hnot
  simp [hx, hnot]
noncomputable def restrictLp (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.restrict D) :=
  ((Lp.memLp f).restrict D).toLp f
lemma restrictLp_coe (f : Lp ℂ 2 μ) :
    (restrictLp D f : X → ℂ) =ᵐ[μ.restrict D] f := MemLp.coeFn_toLp _
lemma extend_restrict (f : Lp ℂ 2 μ) : extendLp D hD (restrictLp D f) = mask D hD f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hD).mp (restrictLp_coe D f)
  filter_upwards [extendLp_coe D hD (restrictLp D f), mask_coe D hD f, hr] with x h₁ h₂ h₃
  rw [h₁,h₂]
  by_cases hx : x ∈ D
  · simpa only [Set.indicator_of_mem hx] using h₃ hx
  · simp [hx]
lemma extend_restrict_supported (f : Lp ℂ 2 μ) (hf : f ∈ supported D) :
    extendLp D hD (restrictLp D f) = f := by
  rw [extend_restrict, (mask_eq_self_iff D hD f).mpr hf]
end Restrict
end HeatL2

open MeasureTheory FourierTransform Filter Set
open scoped ComplexInnerProductSpace
namespace HeatL2

lemma weighted_rpow_jensen {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g v : X → ℝ} (hg : Measurable g) (hgi : Integrable g μ)
    (hgn : ∀ x, 0 ≤ g x) (hg1 : ∫ x, g x ∂μ = 1)
    (hv : Measurable v) (hv01 : ∀ x, v x ∈ Icc (0:ℝ) 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, v x * g x ∂μ)^p ≤ ∫ x, (v x)^p * g x ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have : IsProbabilityMeasure ν := by
    apply isProbabilityMeasure_iff.mpr
    change μ.withDensity (fun x => ENNReal.ofReal (g x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn), hg1]
    norm_num
  have he (f : X → ℝ) : (∫ x, f x ∂ν) = ∫ x, f x * g x ∂μ := by
    change (∫ x, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (g x)))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f]
    simp only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul, mul_comm (g _)]
  have hcont : Continuous (fun x : ℝ => x^p) := Real.continuous_rpow_const (by positivity)
  have hi : Integrable v ν := Integrable.of_bound hv.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv01 x).1]; exact (hv01 x).2)
  have hip : Integrable (fun x => (v x)^p) ν := Integrable.of_bound
    (hcont.measurable.comp hv).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hv01 x).1 _)]
      exact Real.rpow_le_one (hv01 x).1 (hv01 x).2 (by linarith))
  have h := (convexOn_rpow hp).map_integral_le hcont.continuousOn isClosed_Ici
    (ae_of_all ν fun x => (hv01 x).1) hi hip
  simpa only [Pi.neg_apply, he] using h

section Form
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma heat_inner_integral (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, heat w hw hn f⟫).re = ∫ ξ, Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2 := by
  rw [heat, spectralOp_inner]
  rfl

lemma heat_form_rpow (w : E → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    {t η : ℝ} (hη : 0 < η) (hηt : η ≤ t)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : ‖f‖ = 1) :
    ((⟪f, heat (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ)) f⟫).re) ^ (t/η) ≤
    (⟪f, heat (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ)) f⟫).re := by
  simp only [heat_inner_integral]
  have hg1 : (∫ ξ, ‖(𝓕 f) ξ‖^2) = 1 := by
    rw [← norm_sq_integral, Lp.norm_fourier_eq, hf, one_pow]
  have h := weighted_rpow_jensen
    ((Lp.stronglyMeasurable (𝓕 f)).measurable.norm.pow_const 2)
    ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    (fun _ => sq_nonneg _) hg1 ((hw.const_mul η).neg.exp)
    (fun ξ => ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hη.le (hn ξ)))⟩)
    ((one_le_div hη).mpr hηt)
  have he (ξ : E) : Real.exp (-(η*w ξ)) ^ (t/η) = Real.exp (-(t*w ξ)) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  simpa only [Pi.neg_apply, he] using h

end Form
end HeatL2

open MeasureTheory ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma inner_translate_integral (a : E) (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, translate a f⟫ = ∫ x, f (x+a) * conj (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translate_coe a f] with x hx
  simp only [RCLike.inner_apply, hx]

omit [FiniteDimensional ℝ F] in
lemma integrable_translate_pair (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) (ν.prod volume) := by
  have hm : StronglyMeasurable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) := by
    exact ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).mul
      (continuous_star.comp_stronglyMeasurable ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro z
    apply (L2.integrable_inner (𝕜 := ℂ) g (translate (A z) f)).congr
    filter_upwards [translate_coe (A z) f] with x hx
    simp only [RCLike.inner_apply, hx]
  · apply Integrable.mono' (integrable_const (‖f‖^2+‖g‖^2)) hm.norm.aestronglyMeasurable.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hfi : Integrable (fun x => ‖f (x+A z)‖^2) volume := (measurePreserving_add_right volume (A z)).integrable_comp_of_integrable
      ((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    have hgi := (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
    calc
      _ ≤ ∫ x, ‖f (x+A z)‖^2+‖g x‖^2 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hfi.add hgi)
        apply Filter.Eventually.of_forall
        intro x
        change ‖f (x+A z)*conj (g x)‖ ≤ ‖f (x+A z)‖^2+‖g x‖^2
        simp only [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖f (x+A z)‖-‖g x‖)]
      _ = _ := by
        rw [integral_add hfi hgi, integral_add_right_eq_self (fun x => ‖f x‖^2) (A z),
          ← norm_sq_integral, ← norm_sq_integral]

lemma inner_average_spatial (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ x, ∫ z, f (x+A z)*conj (g x) ∂ν := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  simp_rw [inner_translate_integral]
  exact integral_integral_swap (integrable_translate_pair A ν f g)

end Spatial
section Density
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma inner_average_density (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average (ContinuousLinearMap.id ℝ E) ν f⟫ =
      ∫ x, ∫ y, (p (y-x) : ℂ) * f y * conj (g x) := by
  rw [inner_average_spatial]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [hν, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpn _), ContinuousLinearMap.id_apply,
    Complex.real_smul, mul_assoc]
  have he (z : E) : (p z : ℂ)*(f (x+z)*conj (g x)) =
      (p ((z+x)-x) : ℂ)*(f (z+x)*conj (g x)) := by simp [add_comm]
  simp_rw [he]
  exact integral_add_right_eq_self (μ := (volume : Measure E))
    (fun y => (p (y-x) : ℂ)*(f y*conj (g x))) x

noncomputable def densityKernel (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x)
    (hpb : ∀ x, p x ≤ p 0) : BoundedKernel E where
  value xy := p (xy.2-xy.1)
  measurable := hp.comp (measurable_snd.sub measurable_fst)
  nonneg _ := hpn _
  bound := p 0
  bound_nonneg := hpn _
  le_bound _ := hpb _

variable (D : Set E) (hD : MeasurableSet D)

lemma integral_extend_mul (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * (extendLp D hD f) x) = ∫ x in D, a x * f x := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*f y) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma integral_extend_conj (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * conj ((extendLp D hD f) x)) = ∫ x in D, a x * conj (f x) := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*conj (f y)) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma inner_extend (f : Lp ℂ 2 (volume.restrict D)) (g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, extendLp D hD f⟫ = ⟪restrictLp D g, f⟫ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in D, conj (g x)*f x := by
      simpa only [RCLike.inner_apply, mul_comm] using integral_extend_mul D hD f (fun x => conj (g x))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restrictLp_coe D g] with x hx
      simp only [RCLike.inner_apply, hx, mul_comm]

lemma densityKernel_inner (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f g : Lp ℂ 2 (volume.restrict D)) :
    ⟪extendLp D hD g, average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)⟫ =
      ⟪g, kernelOp (densityKernel p hp hpn hpb) f⟫ := by
  rw [inner_average_density ν p hp hpn hν, inner_kernel]
  simp only [densityKernel]
  calc
    _ = ∫ x, (∫ y in D, (p (y-x) : ℂ)*f y)*conj ((extendLp D hD g) x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [integral_mul_const, integral_extend_mul D hD f]
    _ = ∫ x in D, (∫ y in D, (p (y-x) : ℂ)*f y)*conj (g x) :=
      integral_extend_conj D hD g _
    _ = _ := by simp only [integral_mul_const]

lemma extend_kernel_eq (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f : Lp ℂ 2 (volume.restrict D)) :
    extendLp D hD (kernelOp (densityKernel p hp hpn hpb) f) =
      mask D hD (average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_extend, ← mask_inner, ← extend_restrict,
    densityKernel_inner D hD ν p hp hpn hpb hν]

include hD in
lemma restrictLp_norm_le (f : Lp ℂ 2 (volume : Measure E)) : ‖restrictLp D f‖ ≤ ‖f‖ := by
  rw [← extendLp_norm D hD (restrictLp D f), extend_restrict]
  exact mask_norm_le D hD f

lemma compressedAverage_kernel_norm (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] :
    ‖mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD‖ =
      ‖kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)‖ := by
  let T := mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD
  let K := kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)
  change ‖T‖ = ‖K‖
  have he f : T f = extendLp D hD (K (restrictLp D f)) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν, extend_restrict]
    rfl
  have he' f : extendLp D hD (K f) = T (extendLp D hD f) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν]
    change _ = mask D hD (average _ ν (mask D hD (extendLp D hD f)))
    rw [(mask_eq_self_iff D hD _).mpr (extendLp_supported D hD f)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [he, extendLp_norm]
    exact (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (restrictLp_norm_le D hD f) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [← extendLp_norm D hD (K f), he']
    simpa only [extendLp_norm] using T.le_opNorm (extendLp D hD f)

end Density
end HeatL2

end

end OAI
