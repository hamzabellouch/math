import OAI.Analysis.LipschitzHilbert.Fourier.ComplexLineAverage
import OAI.Analysis.LipschitzHilbert.Fourier.HighFrequencyAverage
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzBandPrimitive

namespace OAI

/-! Scalar complex packet averages on the actual line grid. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem integral_complex_square (μ : Measure ℝ) (f : ℝ → ℂ)
    (hre : MemLp (fun x => (f x).re) 2 μ)
    (him : MemLp (fun x => (f x).im) 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) =
      (∫ x, (f x).re ^ 2 ∂μ) + ∫ x, (f x).im ^ 2 ∂μ := by
  have h (x : ℝ) : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq (f x)).symm
  simp_rw [h]
  exact integral_add hre.integrable_sq him.integrable_sq

theorem schwartz_projection_deriv (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    deriv (f.postcompCLM L) = fun x => L (deriv f x) := by
  funext x
  exact (L.hasFDerivAt.comp_hasDerivAt x (f.differentiable x).hasDerivAt).deriv

theorem schwartz_projection_coe (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    (f.postcompCLM L : ℝ → ℝ) = fun x => L (f x) := by
  funext x
  rfl

theorem schwartz_re_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).re) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.reCLM_apply] using
    (f.postcompCLM Complex.reCLM).memLp 2 volume

theorem schwartz_im_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).im) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.imCLM_apply] using
    (f.postcompCLM Complex.imCLM).memLp 2 volume

namespace FiniteLineGrid

def scalarAverage (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (n : ℕ) (x : ℝ) : ℂ :=
  (g.average μ (fun y => (f y).re) n x : ℂ) +
    g.average μ (fun y => (f y).im) n x * Complex.I

@[simp] theorem scalarAverage_re (g : FiniteLineGrid) (μ : Measure ℝ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    (g.scalarAverage μ f n x).re = g.average μ (fun y => (f y).re) n x := by
  simp [scalarAverage]

@[simp] theorem scalarAverage_im (g : FiniteLineGrid) (μ : Measure ℝ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    (g.scalarAverage μ f n x).im = g.average μ (fun y => (f y).im) n x := by
  simp [scalarAverage]

theorem schwartz_projection_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    (L : ℂ →L[ℝ] ℝ) {level : ℕ} (hl : level ≤ g.depth)
    {δ : ℝ} (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (fun y => L (f y)) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, L (A x) ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, L (f x) ^ 2 := by
  let B := A.postcompCLM L
  have hd : deriv B = fun x => L (f x) := by
    rw [schwartz_projection_deriv]
    simp only [hderiv]
  have hc : Continuous (deriv B) := by rw [hd]; exact L.continuous.comp f.continuous
  have hm : MemLp (deriv B) 2 volume := by
    rw [hd]
    exact (f.postcompCLM L).memLp 2
  have h := g.primitive_average_energy B B.differentiable hc (B.memLp 2) hm hl hδ hδmesh
  simpa only [hd, B, SchwartzMap.postcompCLM_apply] using h

theorem schwartz_primitive_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ}
    (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, ‖A x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  have hRe := g.schwartz_projection_average_energy A f hderiv Complex.reCLM hl hδ hδmesh
  have hIm := g.schwartz_projection_average_energy A f hderiv Complex.imCLM hl hδ hδmesh
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  rw [integral_complex_square g.lineMeasure _
    (by simpa only [scalarAverage_re] using g.average_memLp g.lineMeasure _ hre level)
    (by simpa only [scalarAverage_im] using g.average_memLp g.lineMeasure _ him level)]
  simp only [scalarAverage_re, scalarAverage_im]
  rw [integral_complex_square volume A (schwartz_re_memLp A) (schwartz_im_memLp A),
    integral_complex_square volume f (schwartz_re_memLp f) (schwartz_im_memLp f)]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  nlinarith only [hRe, hIm]

theorem schwartz_high_frequency_average (g : FiniteLineGrid)
    (f : SchwartzMap ℝ ℂ) {r R : ℝ} (hr : 0 < r)
    (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth)
    (hmesh : (2 * Real.pi * r)⁻¹ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (16 * (2 * Real.pi * r)⁻¹ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨A,hd,hlo,_⟩ := exists_schwartz_band_primitive f hr hlow hhigh
  have hδ : 0 < (2 * Real.pi * r)⁻¹ := inv_pos.mpr (by positivity)
  have hav := g.schwartz_primitive_average_energy A f hd hl hδ hmesh
  have hp := schwartz_primitive_energy A f hr hd hlo
  have hcoef : 0 ≤ 8 / (g.meshWidth level * (2 * Real.pi * r)⁻¹) :=
    div_nonneg (by norm_num) (mul_pos (g.meshWidth_pos level) hδ).le
  calc
    _ ≤ (8 / (g.meshWidth level * (2 * Real.pi * r)⁻¹)) *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) +
        (8 * (2 * Real.pi * r)⁻¹ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 :=
      hav.trans (add_le_add (mul_le_mul_of_nonneg_left hp hcoef) le_rfl)
    _ = _ := by field_simp; ring

theorem schwartz_poincare (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  have hRe := g.poincare (f.postcompCLM Complex.reCLM) hre
    (f.postcompCLM Complex.reCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.reCLM_apply] using schwartz_re_memLp df) hl
  have hIm := g.poincare (f.postcompCLM Complex.imCLM) him
    (f.postcompCLM Complex.imCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.imCLM_apply] using schwartz_im_memLp df) hl
  have hRe' : (∫ x in g.root, (deriv f x).re ^ 2) ≤ ∫ x, (deriv f x).re ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_re_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have hIm' : (∫ x in g.root, (deriv f x).im ^ 2) ≤ ∫ x, (deriv f x).im ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_im_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have her : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).re)
      2 g.lineMeasure := by
    convert hre.sub (g.average_memLp g.lineMeasure _ hre level) using 1
    ext x
    simp only [Pi.sub_apply, Complex.sub_re, scalarAverage_re]
  have hei : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).im)
      2 g.lineMeasure := by
    convert him.sub (g.average_memLp g.lineMeasure _ him level) using 1
    ext x
    simp only [Pi.sub_apply, Complex.sub_im, scalarAverage_im]
  rw [integral_complex_square g.lineMeasure _ her hei]
  have hdecomp := integral_complex_square volume df (schwartz_re_memLp df) (schwartz_im_memLp df)
  simp only [df, SchwartzMap.derivCLM_apply] at hdecomp
  rw [hdecomp]
  rw [schwartz_projection_deriv] at hRe hIm
  simp only [schwartz_projection_coe, SchwartzMap.postcompCLM_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  simp only [Complex.sub_re, Complex.sub_im, scalarAverage_re, scalarAverage_im]
  exact (add_le_add hRe hIm).trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left hRe' (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hIm' (sq_nonneg _)))

theorem schwartz_low_frequency_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (g.meshWidth level * (2 * Real.pi * R)) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ ≤ g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := g.schwartz_poincare f hl
    _ ≤ g.meshWidth level ^ 2 * ((2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (schwartz_band_derivative_upper f hR hband) (sq_nonneg _)
    _ = _ := by ring

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
