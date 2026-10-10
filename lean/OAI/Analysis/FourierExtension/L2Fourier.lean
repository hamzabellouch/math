import Mathlib

namespace OAI

/-! Bounded pullback densities and graph Fourier L4 estimates. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter

open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace DiagonalExtension.BoundedPullback

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → β} {K : ℝ≥0∞}

lemma comp_memLp (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν)
    (v : Lp ℂ 2 ν) : MemLp (fun x => v (T x)) 2 μ :=
  (((Lp.memLp v).of_measure_le_smul hK h).comp_of_map hT.aemeasurable)

lemma comp_ae (hT : Measurable T) (h : Measure.map T μ ≤ K • ν)
    {f g : β → ℂ} (hfg : f =ᵐ[ν] g) : (fun x => f (T x)) =ᵐ[μ] (fun x => g (T x)) :=
  ae_of_ae_map hT.aemeasurable ((Measure.absolutelyContinuous_of_le_smul h).ae_eq hfg)

def pullbackLinear (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (comp_memLp hT hK h v).toLp (fun x => v (T x))
  map_add' v w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (comp_memLp hT hK h (v + w)),
      Lp.coeFn_add ((comp_memLp hT hK h v).toLp _)
        ((comp_memLp hT hK h w).toLp _),
      MemLp.coeFn_toLp (comp_memLp hT hK h v),
      MemLp.coeFn_toLp (comp_memLp hT hK h w),
      comp_ae hT h (Lp.coeFn_add v w)] with x hx ha hv hw hc
    simpa only [Pi.add_apply, hx, ha, hv, hw] using hc
  map_smul' a v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (comp_memLp hT hK h (a • v)),
      Lp.coeFn_smul a ((comp_memLp hT hK h v).toLp _),
      MemLp.coeFn_toLp (comp_memLp hT hK h v),
      comp_ae hT h (Lp.coeFn_smul a v)] with x hx ha hv hc
    simpa only [Pi.smul_apply, hx, ha, hv, RingHom.id_apply] using hc

lemma pullbackLinear_ae (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν)
    (v : Lp ℂ 2 ν) : pullbackLinear hT hK h v =ᵐ[μ] fun x => v (T x) :=
  MemLp.coeFn_toLp (comp_memLp hT hK h v)

lemma enorm_pullbackLinear_le (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞))
    (h : Measure.map T μ ≤ K • ν) (v : Lp ℂ 2 ν) :
    ‖pullbackLinear hT hK h v‖ₑ ≤ K ^ (1 / 2 : ℝ) * ‖v‖ₑ := by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (pullbackLinear_ae hT hK h v)]
  change eLpNorm ((v : β → ℂ) ∘ T) 2 μ ≤ K ^ (1 / 2 : ℝ) * eLpNorm (v : β → ℂ) 2 ν
  rw [← eLpNorm_map_measure ((Lp.memLp v).of_measure_le_smul hK h).aestronglyMeasurable
    hT.aemeasurable]
  convert eLpNorm_le_of_measure_le_smul (f := (v : β → ℂ)) (p := 2) h using 1
  norm_num

lemma norm_pullbackLinear_le (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞))
    (h : Measure.map T μ ≤ K • ν) (v : Lp ℂ 2 ν) :
    ‖pullbackLinear hT hK h v‖ ≤ K.toReal ^ (1 / 2 : ℝ) * ‖v‖ := by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top, hK])
    (enorm_pullbackLinear_le hT hK h v)

def pullback (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (pullbackLinear hT hK h).mkContinuous (K.toReal ^ (1 / 2 : ℝ))
    (norm_pullbackLinear_le hT hK h)

lemma pullback_ae (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν)
    (v : Lp ℂ 2 ν) : pullback hT hK h v =ᵐ[μ] fun x => v (T x) :=
  pullbackLinear_ae hT hK h v

lemma norm_pullback_le (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν) :
    ‖pullback hT hK h‖ ≤ K.toReal ^ (1 / 2 : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg ENNReal.toReal_nonneg _) _

theorem exists_density (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν)
    (f : Lp ℂ 2 μ) : ∃ u : Lp ℂ 2 ν,
      ‖u‖ ≤ K.toReal ^ (1 / 2 : ℝ) * ‖f‖ ∧
      ∀ v : Lp ℂ 2 ν, inner ℂ u v = ∫ x, inner ℂ (f x) (v (T x)) ∂μ := by
  let A := pullback hT hK h
  refine ⟨ContinuousLinearMap.adjoint A f, ?_, ?_⟩
  · calc
      _ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖A‖ * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ _ := mul_le_mul_of_nonneg_right (norm_pullback_le hT hK h) (norm_nonneg f)
  · intro v
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [pullback_ae hT hK h v] with x hx
    rw [hx]

end DiagonalExtension.BoundedPullback

namespace DiagonalExtension.BoundedPullback
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → β} {K : ℝ≥0∞}

theorem exists_density_mul (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞)) (h : Measure.map T μ ≤ K • ν)
    (f : Lp ℂ 2 μ) : ∃ u : Lp ℂ 2 ν,
      ‖u‖ ≤ K.toReal ^ (1 / 2 : ℝ) * ‖f‖ ∧
      ∀ v : β → ℂ, MemLp v 2 ν → (∫ y, u y * v y ∂ν) = ∫ x, f x * v (T x) ∂μ := by
  obtain ⟨u, hu, hident⟩ := exists_density hT hK h f
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hcv : MemLp (fun y => star (v y)) 2 ν := hv.star
  let cv := hcv.toLp (fun y => star (v y))
  have hcoe : (cv : β → ℂ) =ᵐ[ν] fun y => star (v y) := MemLp.coeFn_toLp hcv
  have heq := congrArg (starRingEnd ℂ) (hident cv)
  rw [L2.inner_def, ← integral_conj, ← integral_conj] at heq
  convert heq using 1
  · apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    simp [hy, RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [comp_ae hT h hcoe] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]

lemma map_restrict_le_restrict {P : Set α} {S : Set β} (hP : MeasurableSet P)
    (hS : MeasurableSet S) (hT : Measurable T) (himage : Set.MapsTo T P S)
    (h : Measure.map T μ ≤ K • ν) :
    Measure.map T (μ.restrict P) ≤ K • ν.restrict S := by
  rw [← Measure.restrict_smul]
  have hle : Measure.map T (μ.restrict P) ≤ Measure.map T μ := Measure.map_mono Measure.restrict_le_self hT
  have hsupport : (Measure.map T (μ.restrict P)).restrict S = Measure.map T (μ.restrict P) := by
    apply Measure.restrict_eq_self_of_ae_mem
    change (Measure.map T (μ.restrict P)) Sᶜ = 0
    rw [Measure.map_apply hT hS.compl, Measure.restrict_apply' hP]
    convert measure_empty (μ := μ) using 2
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => hx.1 (himage hx.2)
  rw [← hsupport]
  exact Measure.restrict_mono (Set.Subset.refl _) (hle.trans h)

end DiagonalExtension.BoundedPullback

namespace DiagonalExtension.BoundedPullback
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → β} {K : ℝ≥0∞}

lemma density_support (hT : Measurable T) (h : Measure.map T μ ≤ K • ν)
    (f : Lp ℂ 2 μ) (u : Lp ℂ 2 ν) {S : Set β} (hS : MeasurableSet S)
    (hf : ∀ᵐ x ∂μ, T x ∉ S → f x = 0)
    (hident : ∀ v : Lp ℂ 2 ν, inner ℂ u v = ∫ x, inner ℂ (f x) (v (T x)) ∂μ) :
    ∀ᵐ y ∂ν, y ∉ S → u y = 0 := by
  classical
  have ho : MemLp (Sᶜ.indicator (u : β → ℂ)) 2 ν := (Lp.memLp u).indicator hS.compl
  let out := ho.toLp _
  have hout : (out : β → ℂ) =ᵐ[ν] Sᶜ.indicator (u : β → ℂ) := MemLp.coeFn_toLp ho
  have hzero : inner ℂ u out = 0 := by
    rw [hident]
    apply integral_eq_zero_of_ae
    filter_upwards [hf, comp_ae hT h hout] with x hx ho
    by_cases hs : T x ∈ S
    · simp [ho, hs]
    · simp [hx hs]
  have hself : inner ℂ out out = 0 := by
    rw [← hzero, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hout] with y hy
    by_cases hs : y ∈ S <;> simp [hy, hs]
  have houtzero : out = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hself
  have hzae : (out : β → ℂ) =ᵐ[ν] 0 := by rw [houtzero]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hout, hzae] with y hy hz
  intro hs
  simpa [hs] using hy.symm.trans hz

theorem exists_integrable_density (hT : Measurable T) (hK : K ≠ (⊤ : ℝ≥0∞))
    (h : Measure.map T μ ≤ K • ν) (f : Lp ℂ 2 μ) {S : Set β}
    (hS : MeasurableSet S) (hSf : ν S < (⊤ : ℝ≥0∞))
    (hf : ∀ᵐ x ∂μ, T x ∉ S → f x = 0) :
    ∃ u : Lp ℂ 2 ν, Integrable (u : β → ℂ) ν ∧
      ‖u‖ ≤ K.toReal ^ (1 / 2 : ℝ) * ‖f‖ ∧
      (∀ᵐ y ∂ν, y ∉ S → u y = 0) ∧
      ∀ v : β → ℂ, MemLp v 2 ν → (∫ y, u y * v y ∂ν) = ∫ x, f x * v (T x) ∂μ := by
  obtain ⟨u, hu, hid⟩ := exists_density hT hK h f
  have hsupp := density_support hT h f u hS hf hid
  have ha : (u : β → ℂ) =ᵐ[ν] S.indicator (u : β → ℂ) := by
    filter_upwards [hsupp] with y hy
    by_cases hs : y ∈ S
    · simp [hs]
    · simp [hs, hy hs]
  have hint : Integrable (u : β → ℂ) ν := by
    have huS : MemLp (u : β → ℂ) 2 (ν.restrict S) := (Lp.memLp u).restrict _
    have : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hSf⟩
    have hi := huS.integrable (by norm_num)
    exact ((integrable_indicator_iff hS).mpr hi).congr ha.symm
  refine ⟨u, hint, hu, hsupp, ?_⟩
  intro v hv
  have hcv : MemLp (fun y => star (v y)) 2 ν := hv.star
  let cv := hcv.toLp (fun y => star (v y))
  have hcoe : (cv : β → ℂ) =ᵐ[ν] fun y => star (v y) := MemLp.coeFn_toLp hcv
  have heq := congrArg (starRingEnd ℂ) (hid cv)
  rw [L2.inner_def, ← integral_conj, ← integral_conj] at heq
  convert heq using 1
  · apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    simp [hy, RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [comp_ae hT h hcoe] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]

end DiagonalExtension.BoundedPullback

namespace DiagonalExtension.BoundedPullback
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → β} {K : ℝ≥0∞}

lemma density_bounded_test (f : Lp ℂ 2 μ) (u : Lp ℂ 2 ν) {S : Set β}
    (hS : MeasurableSet S) (hSf : ν S < (⊤ : ℝ≥0∞))
    (hf : ∀ᵐ x ∂μ, T x ∉ S → f x = 0) (hu : ∀ᵐ y ∂ν, y ∉ S → u y = 0)
    (hid : ∀ v : β → ℂ, MemLp v 2 ν → (∫ y, u y * v y ∂ν) = ∫ x, f x * v (T x) ∂μ)
    {v : β → ℂ} (hv : AEStronglyMeasurable v ν) (C : ℝ) (hC : ∀ y, ‖v y‖ ≤ C) :
    (∫ y, u y * v y ∂ν) = ∫ x, f x * v (T x) ∂μ := by
  classical
  have : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hSf⟩
  have hvi : MemLp (S.indicator v) 2 ν := by
    rw [memLp_indicator_iff_restrict hS]
    exact MemLp.of_bound hv.restrict C (Filter.Eventually.of_forall hC)
  calc
    _ = ∫ y, u y * S.indicator v y ∂ν := by
      apply integral_congr_ae
      filter_upwards [hu] with y hy
      by_cases hs : y ∈ S
      · simp [hs]
      · simp [hs, hy hs]
    _ = ∫ x, f x * S.indicator v (T x) ∂μ := hid _ hvi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hs : T x ∈ S
      · simp [hs]
      · simp [hs, hx hs]

end DiagonalExtension.BoundedPullback

open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace DiagonalExtension.TensorL2
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma memLp_mul_prod {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((hf.aestronglyMeasurable.comp_fst).mul (hg.aestronglyMeasurable.comp_snd))).mpr
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq

lemma norm_sq_toLp {γ : Type*} [MeasurableSpace γ] {m : Measure γ}
    {f : γ → ℂ} (hf : MemLp f 2 m) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂m := by
  apply Complex.ofReal_injective
  have hi : ((‖hf.toLp f‖ ^ 2 : ℝ) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by simp
  rw [hi, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, inner_self_eq_norm_sq_to_K]

lemma norm_mul_prod {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    ‖(memLp_mul_prod hf hg).toLp (fun z : α × β => f z.1 * g z.2)‖ =
      ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hs : ‖(memLp_mul_prod hf hg).toLp (fun z : α × β => f z.1 * g z.2)‖ ^ 2 =
      (‖hf.toLp f‖ * ‖hg.toLp g‖)^2 := by
    simp only [mul_pow, norm_sq_toLp, norm_mul]
    exact integral_prod_mul (fun x => ‖f x‖ ^ 2) (fun y => ‖g y‖ ^ 2)
  nlinarith [norm_nonneg ((memLp_mul_prod hf hg).toLp (fun z : α × β => f z.1 * g z.2)),
    mul_nonneg (norm_nonneg (hf.toLp f)) (norm_nonneg (hg.toLp g))]

end DiagonalExtension.TensorL2

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal
namespace DiagonalExtension.FourierCompatibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_fourier_swap {f : E → ℂ} (hf : Integrable f) (v : 𝓢(E, ℂ)) :
    (∫ x, v x * 𝓕 f x) = ∫ x, 𝓕 v x * f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner hf (v.integrable (μ := volume))
  simp only [flip_innerₗ] at h
  change (∫ x, 𝓕 f x * v x) = ∫ x, f x * 𝓕 (v : E → ℂ) x at h
  simpa only [mul_comm, SchwartzMap.fourier_coe] using h

theorem fourier_ae (f : Lp ℂ 2 (volume : Measure E)) (hf : Integrable (f : E → ℂ)) :
    𝓕 (f : E → ℂ) =ᵐ[volume] (𝓕 f : Lp ℂ 2 volume) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable
  · exact (Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num)
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg
  let v : 𝓢(E, ℂ) := hg₁.toSchwartzMap hg₂
  have hd := congrArg (fun D : 𝓢'(E, ℂ) => D v) (Lp.fourier_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  calc
    _ = ∫ x, v x * 𝓕 (f : E → ℂ) x := by simp [v, Complex.real_smul]
    _ = ∫ x, 𝓕 v x * f x := integral_fourier_swap hf v
    _ = ∫ x, v x * (𝓕 f : Lp ℂ 2 volume) x := hd
    _ = _ := by simp [v, Complex.real_smul]

lemma fourier_memLp {f : E → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 := by
  have hcoe := MemLp.coeFn_toLp hf2
  have hF := fourier_ae (hf2.toLp f) (hf.congr hcoe.symm)
  have he : 𝓕 (hf2.toLp f : E → ℂ) = 𝓕 f := by
    ext x
    rw [Real.fourier_eq, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    rw [hy]
  rw [he] at hF
  exact MemLp.ae_eq hF.symm (Lp.memLp (𝓕 (hf2.toLp f)))

end DiagonalExtension.FourierCompatibility

open MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace
namespace DiagonalExtension.GraphFourier
variable {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def transform (Γ : X → E) (g : X → ℂ) (x : E) : ℂ :=
  ∫ ξ, g ξ * (Real.fourierChar (-inner ℝ (Γ ξ) x) : ℂ)

def pairMap (Γ : X → E) (z : X × X) : E := Γ z.1 + Γ z.2

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairMap_continuous {Γ : X → E} (hΓ : Continuous Γ) : Continuous (pairMap Γ) :=
  (hΓ.comp continuous_fst).add (hΓ.comp continuous_snd)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma character_continuous (x : E) :
    Continuous (fun y : E => (Real.fourierChar (-inner ℝ y x) : ℂ)) :=
  (show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_transform {Γ : X → E} (hΓ : Continuous Γ) {g : X → ℂ}
    (hg : Integrable g) : Continuous (transform Γ g) := by
  apply continuous_of_dominated
    (fun x => hg.aestronglyMeasurable.mul ((character_continuous x).comp hΓ).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun ξ => by
      change ‖g ξ * (Real.fourierChar (-inner ℝ (Γ ξ) x) : ℂ)‖ ≤ ‖g ξ‖
      rw [norm_mul, Circle.norm_coe, mul_one])) hg.norm
  apply Filter.Eventually.of_forall
  intro ξ
  exact continuous_const.mul ((show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id).neg))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma character_add (a b x : E) :
    (Real.fourierChar (-inner ℝ (a + b) x) : ℂ) =
      (Real.fourierChar (-inner ℝ a x) : ℂ) * (Real.fourierChar (-inner ℝ b x) : ℂ) := by
  rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem square_density {Γ : X → E} (hΓ : Continuous Γ) {K : ℝ≥0∞} (hK : K ≠ (⊤ : ℝ≥0∞))
    (hmap : Measure.map (pairMap Γ) (volume.prod volume) ≤ K • volume)
    {g : X → ℂ} (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    ∃ u : Lp ℂ 2 (volume : Measure E), Integrable (u : E → ℂ) ∧
      ‖u‖ ≤ K.toReal ^ (1 / 2 : ℝ) * ‖hg.toLp g‖ ^ 2 ∧
      ∀ x : E, 𝓕 (u : E → ℂ) x = transform Γ g x ^ 2 := by
  classical
  let T := pairMap Γ
  have hT : Continuous T := pairMap_continuous hΓ
  let S := T '' (tsupport g ×ˢ tsupport g)
  have hcomp : IsCompact S := (hgc.isCompact.prod hgc.isCompact).image hT
  have hF := TensorL2.memLp_mul_prod hg hg
  let F : Lp ℂ 2 (volume.prod volume) := hF.toLp (fun z : X × X => g z.1 * g z.2)
  have hFeq : (F : X × X → ℂ) =ᵐ[volume.prod volume] fun z => g z.1 * g z.2 :=
    MemLp.coeFn_toLp hF
  have hsupp : ∀ᵐ z ∂volume.prod volume, T z ∉ S → F z = 0 := by
    filter_upwards [hFeq] with z hz
    intro hout
    rw [hz]
    by_cases h1 : z.1 ∈ tsupport g
    · have h2 : z.2 ∉ tsupport g := fun h2 => hout ⟨z, ⟨h1, h2⟩, rfl⟩
      simp [image_eq_zero_of_notMem_tsupport h2]
    · simp [image_eq_zero_of_notMem_tsupport h1]
  obtain ⟨u, hu1, hunorm, husupp, huid⟩ := BoundedPullback.exists_integrable_density
    hT.measurable hK hmap F hcomp.measurableSet hcomp.measure_lt_top hsupp
  refine ⟨u, hu1, ?_, ?_⟩
  · change ‖u‖ ≤ _ * ‖(TensorL2.memLp_mul_prod hg hg).toLp (fun z : X × X => g z.1 * g z.2)‖ at hunorm
    rw [TensorL2.norm_mul_prod hg hg] at hunorm
    simpa only [← sq] using hunorm
  intro x
  have hid := BoundedPullback.density_bounded_test F u hcomp.measurableSet
    hcomp.measure_lt_top hsupp husupp huid
    (character_continuous x).aestronglyMeasurable 1 (fun y => by simp only [Circle.norm_coe, le_rfl])
  rw [Real.fourier_eq]
  calc
    _ = ∫ y : E, u y * (Real.fourierChar (-inner ℝ y x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [Circle.smul_def, mul_comm]
    _ = ∫ z, F z * (Real.fourierChar (-inner ℝ (T z) x) : ℂ) ∂volume.prod volume := hid
    _ = ∫ z : X × X, (g z.1 * (Real.fourierChar (-inner ℝ (Γ z.1) x) : ℂ)) *
        (g z.2 * (Real.fourierChar (-inner ℝ (Γ z.2) x) : ℂ)) ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [hFeq] with z hz
      rw [hz]
      change (g z.1 * g z.2) * (Real.fourierChar (-inner ℝ (Γ z.1 + Γ z.2) x) : ℂ) = _
      rw [character_add]
      ring
    _ = transform Γ g x ^ 2 := by
      simpa only [transform, pow_two] using (integral_prod_mul
        (fun ξ => g ξ * (Real.fourierChar (-inner ℝ (Γ ξ) x) : ℂ))
        (fun ξ => g ξ * (Real.fourierChar (-inner ℝ (Γ ξ) x) : ℂ)))

end DiagonalExtension.GraphFourier

namespace DiagonalExtension.GraphFourier
open MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace
variable {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_compact_L2 {g : X → ℂ} (hg : MemLp g 2 volume)
    (hgc : HasCompactSupport g) : Integrable g :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport g)).mp
    ((hg.locallyIntegrable (by norm_num)).integrableOn_isCompact hgc.isCompact)

lemma eLpNorm'_square {α : Type*} [MeasurableSpace α] (μ : Measure α) (G : α → ℂ) :
    eLpNorm' (fun point => G point ^ 2) 2 μ = (eLpNorm' G 4 μ) ^ (2 : ℝ) := by
  calc
    _ = eLpNorm' (fun point => ‖G point‖ ^ (2 : ℝ)) 2 μ := by
      apply eLpNorm'_congr_norm_ae
      filter_upwards [] with point
      simp [norm_pow]
    _ = _ := by
      have identity := eLpNorm'_norm_rpow (μ := μ) G 2 2 (by norm_num)
      norm_num at identity ⊢
      exact identity

lemma eLpNorm_square {α : Type*} [MeasurableSpace α] (μ : Measure α) (G : α → ℂ)
    (hG : AEStronglyMeasurable G μ) :
    eLpNorm (fun point => G point ^ 2) 2 μ = (eLpNorm G 4 μ) ^ (2 : ℝ) := by
  have hsquare : AEStronglyMeasurable (fun point => G point ^ 2) μ := hG.pow 2
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hsquare,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hG]
  norm_num only [ENNReal.toReal_ofNat]
  exact eLpNorm'_square μ G

theorem memLp_four_and_bound {Γ : X → E} (hΓ : Continuous Γ) {K : ℝ≥0∞} (hK : K ≠ (⊤ : ℝ≥0∞))
    (hmap : Measure.map (pairMap Γ) (volume.prod volume) ≤ K • volume)
    {g : X → ℂ} (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    MemLp (transform Γ g) 4 volume ∧
      eLpNorm (transform Γ g) 4 volume ≤ K ^ (1 / 4 : ℝ) * eLpNorm g 2 volume := by
  obtain ⟨u, hu1, hub, hueq⟩ := square_density hΓ hK hmap hg hgc
  have hG : AEStronglyMeasurable (transform Γ g) volume :=
    (continuous_transform hΓ (integrable_compact_L2 hg hgc)).aestronglyMeasurable
  have hFae : (fun x => transform Γ g x ^ 2) =ᵐ[volume] (𝓕 u : Lp ℂ 2 volume) := by
    convert FourierCompatibility.fourier_ae u hu1 using 1
    ext x
    exact (hueq x).symm
  have htwo : MemLp (fun x => transform Γ g x ^ 2) 2 volume :=
    MemLp.ae_eq hFae.symm (Lp.memLp (𝓕 u))
  have hfour : MemLp (transform Γ g) 4 volume := by
    have hn := htwo.norm
    have hm := (memLp_norm_rpow_iff (p := 4) (q := 2) hG (by norm_num) (by norm_num))
    apply hm.mp
    have h42 : (4 : ℝ≥0∞) / 2 = 2 := by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
      norm_num
    simpa [h42] using hn
  refine ⟨hfour, ?_⟩
  have hsq : eLpNorm (transform Γ g) 4 volume ^ (2 : ℝ) = ‖u‖ₑ := by
    rw [← eLpNorm_square _ _ hG, eLpNorm_congr_ae hFae, ← Lp.enorm_def]
    exact enorm_eq_iff_norm_eq.mpr (Lp.norm_fourier_eq u)
  have hub' : ‖u‖ₑ ≤ K ^ (1 / 2 : ℝ) * (eLpNorm g 2 volume) ^ (2 : ℝ) := by
    have hh := ENNReal.ofReal_le_ofReal hub
    simpa only [ofReal_norm, ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
      ENNReal.ofReal_toReal hK, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      Lp.enorm_toLp, ENNReal.rpow_two] using hh
  have hr := ENNReal.rpow_le_rpow (hsq ▸ hub') (by norm_num : (0:ℝ) ≤ 1/2)
  simpa only [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    show (2:ℝ)*(1/2)=1 by norm_num, show (1/2:ℝ)*(1/2)=1/4 by norm_num,
    ENNReal.rpow_one] using hr

end DiagonalExtension.GraphFourier

end

end OAI
