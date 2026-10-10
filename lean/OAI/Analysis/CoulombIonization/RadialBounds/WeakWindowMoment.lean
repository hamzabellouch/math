import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakDirectionalDerivative

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
open scoped LineDeriv

lemma weak_window_moment {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    {v : V} (hw : HasWeakDirectionalDerivative f u v) (g : 𝓢(V, ℝ)) (z : V) :
    Integrable (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
      ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) ∧
    (∫ ξ, (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
      ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) =
      ∫ x, ‖u x * (g (x-z) : ℂ) + f x * (∂_{v} g (x-z) : ℂ)‖^2 := by
  have hfw := weak_window_memLp hf g z
  have huw := (weak_window_memLp hu g z).add (weak_window_memLp hf (∂_{v} g) z)
  have hm := weak_fourier_moment hfw huw (weak_window_derivative hf hu hw g z)
  have he := l2_fourier_ae_classical hfw (weak_window_integrable hf g z)
  have he' : (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
      ‖(𝓕 (hfw.toLp _) : Lp ℂ 2 volume) ξ‖^2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) := by
    filter_upwards [he] with ξ hξ
    rw [hξ]
  exact ⟨hm.1.congr he', (integral_congr_ae he').symm.trans hm.2⟩

lemma norm_complex_real_combination (u f : ℂ) (a b : ℝ) :
    ‖u * (a : ℂ) + f * (b : ℂ)‖^2 =
      a^2 * ‖u‖^2 + b^2 * ‖f‖^2 + 2 * (a*b) * (u.re*f.re+u.im*f.im) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  ring

lemma integrable_shift_mul {F G : V → ℝ} (hF : Integrable F) (hG : Integrable G) :
    Integrable (fun p : V × V => F (p.2-p.1) * G p.2) (volume.prod volume) := by
  have he : MeasurePreserving (fun p : V × V => (p.2-p.1,p.2))
      (volume.prod volume) (volume.prod volume) := by
    simpa only [Function.comp_def, Prod.map_apply, neg_sub, id_eq] using
      ((Measure.measurePreserving_neg (volume : Measure V)).prod
        (MeasurePreserving.id (volume : Measure V))).comp
        (measurePreserving_sub_prod (volume : Measure V) volume)
  exact he.integrable_comp_of_integrable (hF.mul_prod hG)

lemma integral_shift_mul {F G : V → ℝ} (hF : Integrable F) (hG : Integrable G) :
    (∫ z : V, ∫ x : V, F (x-z) * G x) = (∫ y : V, F y) * (∫ x : V, G x) := by
  rw [integral_integral_swap (integrable_shift_mul hF hG)]
  simp_rw [integral_mul_const, integral_sub_left_eq_self F volume]
  rw [integral_const_mul]

lemma schwartz_integrable_sq (g : 𝓢(V, ℝ)) : Integrable (fun x => g x^2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    (memLp_two_iff_integrable_sq_norm (g.memLp 2).aestronglyMeasurable).1 (g.memLp 2)

lemma integral_schwartz_self_derivative (g : 𝓢(V, ℝ)) (v : V) :
    (∫ x : V, g x * ∂_{v} g x) = 0 := by
  have he := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
    (μ := (volume : Measure V)) g g v
  simp_rw [mul_comm (∂_{v} g _) (g _)] at he
  linarith

lemma weak_window_derivative_integrable {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    (g : 𝓢(V, ℝ)) (v : V) :
    Integrable (fun p : V × V =>
      ‖u p.2 * (g (p.2-p.1) : ℂ) + f p.2 * (∂_{v} g (p.2-p.1) : ℂ)‖^2)
      (volume.prod volume) := by
  have hfu : Integrable (fun x => (u x).re*(f x).re+(u x).im*(f x).im) :=
    (hu.re.integrable_mul hf.re).add (hu.im.integrable_mul hf.im)
  have hgg : Integrable (fun x => g x * ∂_{v} g x) :=
    (g.memLp 2).integrable_mul ((∂_{v} g).memLp 2)
  simp_rw [norm_complex_real_combination]
  exact ((integrable_shift_mul (schwartz_integrable_sq g)
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu)).add
    (integrable_shift_mul (schwartz_integrable_sq (∂_{v} g))
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf))).add
      (by simpa only [mul_assoc] using (integrable_shift_mul hgg hfu).const_mul 2)

lemma integrated_weak_window_derivative {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    (g : 𝓢(V, ℝ)) (v : V) :
    (∫ z : V, ∫ x : V,
      ‖u x * (g (x-z) : ℂ) + f x * (∂_{v} g (x-z) : ℂ)‖^2) =
      (∫ x : V, g x^2) * (∫ x : V, ‖u x‖^2) +
        (∫ x : V, (∂_{v} g x)^2) * (∫ x : V, ‖f x‖^2) := by
  have hfu : Integrable (fun x => (u x).re*(f x).re+(u x).im*(f x).im) :=
    (hu.re.integrable_mul hf.re).add (hu.im.integrable_mul hf.im)
  have hgg : Integrable (fun x => g x * ∂_{v} g x) :=
    (g.memLp 2).integrable_mul ((∂_{v} g).memLp 2)
  have hA := integrable_shift_mul (schwartz_integrable_sq g)
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu)
  have hB := integrable_shift_mul (schwartz_integrable_sq (∂_{v} g))
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf)
  have hC := (integrable_shift_mul hgg hfu).const_mul 2
  rw [← integral_prod _ (weak_window_derivative_integrable hf hu g v)]
  simp_rw [norm_complex_real_combination, mul_assoc (2 : ℝ)]
  have hAB : Integrable (fun p : V × V => g (p.2-p.1)^2 * ‖u p.2‖^2 +
      (∂_{v} g (p.2-p.1))^2 * ‖f p.2‖^2) (volume.prod volume) := hA.add hB
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul,
    integral_prod _ hA, integral_prod _ hB, integral_prod _ (integrable_shift_mul hgg hfu),
    integral_shift_mul (schwartz_integrable_sq g)
      ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu),
    integral_shift_mul (schwartz_integrable_sq (∂_{v} g))
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf), integral_shift_mul hgg hfu,
    integral_schwartz_self_derivative, zero_mul, mul_zero, add_zero]

lemma integrated_weak_window_moment {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    {v : V} (hw : HasWeakDirectionalDerivative f u v) (g : 𝓢(V, ℝ)) :
    (∫ z : V, ∫ ξ : V, (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
      ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) =
      (∫ x : V, g x^2) * (∫ x : V, ‖u x‖^2) +
        (∫ x : V, (∂_{v} g x)^2) * (∫ x : V, ‖f x‖^2) := by
  simp_rw [(weak_window_moment hf hu hw g _).2]
  exact integrated_weak_window_derivative hf hu g v

lemma weak_window_fourier_measurable {f : V → ℂ} (hf : MemLp f 2) (g : 𝓢(V, ℝ)) :
    AEStronglyMeasurable (fun p : V × V => 𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2)
      (volume.prod volume) := by
  have hc : Continuous (fun q : (V × V) × V =>
      Real.fourierChar (-inner ℝ q.2 q.1.2)) :=
    Real.continuous_fourierChar.comp ((continuous_snd.inner
      (continuous_snd.comp continuous_fst)).neg)
  have hg : Continuous (fun q : (V × V) × V => (g (q.2-q.1.1) : ℂ)) :=
    Complex.continuous_ofReal.comp (g.continuous.comp
      (continuous_snd.sub (continuous_fst.comp continuous_fst)))
  have hm : AEStronglyMeasurable (fun q : (V × V) × V =>
      Real.fourierChar (-inner ℝ q.2 q.1.2) • (f q.2 * (g (q.2-q.1.1) : ℂ)))
      ((volume.prod volume).prod volume) :=
    hc.aestronglyMeasurable.fun_smul
      (hf.aestronglyMeasurable.comp_snd.mul hg.aestronglyMeasurable)
  convert hm.integral_prod_right' using 1
  ext p
  simp only [Real.fourier_eq]

lemma weak_window_moment_integrable {f u : V → ℂ} (hf : MemLp f 2) (hu : MemLp u 2)
    {v : V} (hw : HasWeakDirectionalDerivative f u v) (g : 𝓢(V, ℝ)) :
    Integrable (fun p : V × V => (2 * Real.pi)^2 * (inner ℝ p.2 v)^2 *
      ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : V × V =>
      (2 * Real.pi)^2 * (inner ℝ p.2 v)^2 *
      ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2) (volume.prod volume) :=
    (((continuous_snd.inner continuous_const).pow 2).const_mul _).aestronglyMeasurable.mul
      ((weak_window_fourier_measurable hf g).norm.pow 2)
  apply (integrable_prod_iff hm).2
  refine ⟨Filter.Eventually.of_forall (fun z => (weak_window_moment hf hu hw g z).1), ?_⟩
  have he (z : V) :
      (∫ ξ : V, ‖(2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2‖) =
      ∫ x : V, ‖u x * (g (x-z) : ℂ) + f x * (∂_{v} g (x-z) : ℂ)‖^2 := by
    simp_rw [Real.norm_of_nonneg (by positivity :
      0 ≤ (2 * Real.pi)^2 * (inner ℝ _ v)^2 * ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) _‖^2)]
    exact (weak_window_moment hf hu hw g z).2
  simp_rw [he]
  exact (weak_window_derivative_integrable hf hu g v).integral_prod_left

lemma weak_window_mass {f : V → ℂ} (hf : MemLp f 2) (g : 𝓢(V, ℝ)) (z : V) :
    Integrable (fun ξ : V => ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) ∧
    (∫ ξ : V, ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) =
      ∫ x : V, ‖f x‖^2 * g (x-z)^2 := by
  have hfw := weak_window_memLp hf g z
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.memLp (𝓕 (hfw.toLp _))).aestronglyMeasurable).1
    (Lp.memLp (𝓕 (hfw.toLp _)))
  have hae := l2_fourier_ae_classical hfw (weak_window_integrable hf g z)
  have he : (fun ξ => ‖(𝓕 (hfw.toLp _) : Lp ℂ 2 volume) ξ‖^2) =ᵐ[volume]
      (fun ξ => ‖𝓕 (fun x => f x * (g (x-z) : ℂ)) ξ‖^2) := by
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  refine ⟨hi.congr he, ?_⟩
  rw [← integral_congr_ae he, ← l2_norm_sq_integral, Lp.norm_fourier_eq, l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hfw.coeFn_toLp] with x hx
  rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma weak_window_kinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f : V → ℂ} {u : ι → V → ℂ} (hf : MemLp f 2) (hu : ∀ i, MemLp (u i) 2)
    (hw : ∀ i, HasWeakDirectionalDerivative f (u i) (b i)) (g : 𝓢(V, ℝ)) :
    Integrable (fun p : V × V => (2 * Real.pi)^2 * ‖p.2‖^2 *
      ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2) (volume.prod volume) ∧
    (∫ p : V × V, (2 * Real.pi)^2 * ‖p.2‖^2 *
      ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2 ∂volume.prod volume) =
      (∫ x : V, g x^2) * (∑ i, ∫ x : V, ‖u i x‖^2) +
        (∑ i, ∫ x : V, (∂_{b i} g x)^2) * (∫ x : V, ‖f x‖^2) := by
  classical
  have he (p : V × V) : (2 * Real.pi)^2 * ‖p.2‖^2 *
      ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2 =
      ∑ i, (2 * Real.pi)^2 * (inner ℝ p.2 (b i))^2 *
        ‖𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2‖^2 := by
    rw [← b.sum_sq_inner_left p.2, Finset.mul_sum, Finset.sum_mul]
  simp_rw [he]
  have hi (i : ι) := weak_window_moment_integrable hf (hu i) (hw i) g
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_prod _ (hi _), integrated_weak_window_moment hf (hu _) (hw _) g]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

end CoulombAtom

open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology

end

end OAI
