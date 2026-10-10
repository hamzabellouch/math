import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
namespace Multiplier
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
def apply (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((memLp_top_of_bound hf C hbound).fun_mul (Lp.memLp g)).toLp (fun x => f x*g x)
lemma apply_ae (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : apply μ f hf hbound g =ᵐ[μ] fun x => f x*g x := MemLp.coeFn_toLp _
def linear (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := apply μ f hf hbound
  map_add' g h := by
    apply Lp.ext
    filter_upwards [apply_ae μ f hf hbound (g+h),apply_ae μ f hf hbound g,apply_ae μ f hf hbound h,
      Lp.coeFn_add g h,Lp.coeFn_add (apply μ f hf hbound g) (apply μ f hf hbound h)] with x ha hb hc hd he
    simp only [ha,he,Pi.add_apply,hb,hc,hd,mul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [apply_ae μ f hf hbound (c • g),apply_ae μ f hf hbound g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (apply μ f hf hbound g)] with x ha hb hc hd
    simp only [RingHom.id_apply,ha,hd,Pi.smul_apply,hb,hc,smul_eq_mul]
    ring
lemma apply_norm_le (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : ‖apply μ f hf hbound g‖ ≤ C*‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [apply_ae μ f hf hbound g,hbound] with x hx hf
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)
def clm (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linear μ f hf hbound).mkContinuous C (apply_norm_le μ f hf hbound)
lemma clm_ae (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : clm μ f hf hbound g =ᵐ[μ] fun x => f x*g x := apply_ae μ f hf hbound g
end Multiplier
abbrev ComplexPlaneL2 := Lp (α := ℂ) ℂ 2 volume
def planeTranslate (h : ℂ) : ComplexPlaneL2 →ₗᵢ[ℂ] ComplexPlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x+h) (measurePreserving_add_right volume h)
lemma planeTranslate_ae (h : ℂ) (g : ComplexPlaneL2) :
    planeTranslate h g =ᵐ[volume] fun x => g (x+h) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right volume h)
def planePhase (h ξ : ℂ) : ℂ := Real.fourierChar (inner ℝ h ξ)
lemma planePhase_norm (h ξ : ℂ) : ‖planePhase h ξ‖=1 := Circle.norm_coe _
lemma planePhase_continuous (h : ℂ) : Continuous (planePhase h) := by
  unfold planePhase
  fun_prop

def phaseMultiplier (h : ℂ) : ComplexPlaneL2 →L[ℂ] ComplexPlaneL2 :=
  Multiplier.clm volume (planePhase h) (planePhase_continuous h).aestronglyMeasurable
    (Eventually.of_forall fun ξ => (planePhase_norm h ξ).le)
lemma phaseMultiplier_ae (h : ℂ) (g : ComplexPlaneL2) :
    phaseMultiplier h g =ᵐ[volume] fun ξ => planePhase h ξ*g ξ := Multiplier.clm_ae _ _ _ _ _
def schwartzTranslate (h : ℂ) : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const h)) (isometry_add_right h).antilipschitzWith
lemma schwartzTranslate_apply (h : ℂ) (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    schwartzTranslate h f x = f (x+h) := rfl
lemma schwartzTranslate_toLp (h : ℂ) (f : SchwartzMap ℂ ℂ) :
    (schwartzTranslate h f).toLp 2 = planeTranslate h (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(schwartzTranslate h f).coeFn_toLp 2,planeTranslate_ae h (f.toLp 2),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)] with x hx hy hz
  exact hx.trans ((schwartzTranslate_apply h f x).trans (hz.symm.trans hy.symm))
lemma fourier_schwartzTranslate (h : ℂ) (f : SchwartzMap ℂ ℂ) (ξ : ℂ) :
    𝓕 (schwartzTranslate h f) ξ = planePhase h ξ * 𝓕 f ξ := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℂ) (f : ℂ → ℂ) h) ξ
  simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,schwartzTranslate_apply,
    planePhase,Circle.smul_def,smul_eq_mul,VectorFourier.fourierIntegral,Function.comp_def,innerₗ_apply_apply] using hh
lemma fourier_planeTranslate (h : ℂ) (g : ComplexPlaneL2) :
    𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g) := by
  apply DenseRange.induction_on (p := fun g : ComplexPlaneL2 => 𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℂ ℂ).continuous.comp (planeTranslate h).continuous)
      ((phaseMultiplier h).continuous.comp (Lp.fourierTransformₗᵢ ℂ ℂ).continuous)
  intro f
  change 𝓕 (planeTranslate h (f.toLp 2)) = phaseMultiplier h (𝓕 (f.toLp 2))
  rw [← schwartzTranslate_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzTranslate h f)).coeFn_toLp 2,phaseMultiplier_ae h ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2] with ξ hξ hmul hf
  rw [hξ,hmul,hf]
  exact fourier_schwartzTranslate h f ξ
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor.ProbabilityL2
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

variable (μ : Measure X) [SFinite μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
def average (F : X × Ω → ℂ) (x : X) : ℂ := ∫ ω, F (x,ω) ∂ν
lemma average_measurable {F : X × Ω → ℂ} (hF : StronglyMeasurable F) :
    StronglyMeasurable (average ν F) := hF.integral_prod_right'
lemma fiber_memLp {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun ω => F (x,ω)) 2 ν := by
  filter_upwards [hF2.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx
lemma average_memLp {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) : MemLp (average ν F) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (average_measurable ν hF).aestronglyMeasurable).mpr
  apply hF2.integral_prod_left.mono' ((average_measurable ν hF).norm.pow 2).aestronglyMeasurable
  filter_upwards [fiber_memLp μ ν hF hF2,hF2.prod_right_ae] with x hx hx2
  simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq,average] using
    norm_integral_sq ν (fun ω => F (x,ω)) (hx.integrable (by norm_num)) hx2
lemma average_toLp_integral {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) (G : Ω → Lp ℂ 2 μ)
    (hG : Integrable G ν) (hrep : ∀ᵐ ω ∂ν, G ω =ᵐ[μ] fun x => F (x,ω)) :
    (average_memLp μ ν hF hF2).toLp (average ν F) = ∫ ω, G ω ∂ν := by
  apply ext_inner_left ℂ
  intro g
  have hg2 : Integrable (fun z : X × Ω => ‖g z.1‖^2) (μ.prod ν) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)).comp_fst ν
  have hpair : Integrable (fun z : X × Ω => inner ℂ (g z.1) (F z)) (μ.prod ν) := by
    apply (hg2.add hF2).mono'
      (((Lp.stronglyMeasurable g).comp_measurable measurable_fst).inner hF).aestronglyMeasurable
    exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
      (by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (‖g z.1‖-‖F z‖)])
  rw [L2.inner_def,← integral_inner hG g]
  calc
    _ = ∫ x, inner ℂ (g x) (average ν F x) ∂μ := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (average_memLp μ ν hF hF2)] with x hx
      rw [hx])
    _ = ∫ x, ∫ ω, inner ℂ (g x) (F (x,ω)) ∂ν ∂μ := integral_congr_ae (by
      filter_upwards [fiber_memLp μ ν hF hF2] with x hx
      exact (integral_inner (hx.integrable (by norm_num)) (g x)).symm)
    _ = ∫ ω, ∫ x, inner ℂ (g x) (F (x,ω)) ∂μ ∂ν := integral_integral_swap hpair
    _ = _ := integral_congr_ae (by
      filter_upwards [hrep] with ω hω
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hω] with x hx
      rw [hx])
end EuclideanFiveColor.ProbabilityL2
end

end OAI
