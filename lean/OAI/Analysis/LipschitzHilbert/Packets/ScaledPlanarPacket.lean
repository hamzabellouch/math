import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzDecay

namespace OAI

/-! General planar Schwartz profiles in the physical packet coordinates.
The affine restriction retains Schwartz regularity and the carrier is
removed exactly by vertical covariant differentiation. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem affineRescale_antilipschitz (a l : ℝ) (hl : l ≠ 0) :
    AntilipschitzWith ‖l‖₊ (fun x : ℝ => (x-a)/l) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [Real.dist_eq, coe_nnnorm]
  have heq : (x-a)/l-(y-a)/l = (x-y)/l := by ring
  rw [heq, abs_div]
  simp only [Real.norm_eq_abs]
  rw [mul_div_cancel₀ _ (abs_ne_zero.mpr hl)]

def scaledPlanarSlice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a l b beta : ℝ) (hl : l ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (g := fun x : ℝ => (x-a)/l) (by simp only [div_eq_mul_inv]; fun_prop)
    (affineRescale_antilipschitz a l hl) (planarSchwartzSlice f b beta)

@[simp] theorem scaledPlanarSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a l b beta : ℝ) (hl : l ≠ 0) (x : ℝ) :
    scaledPlanarSlice f a l b beta hl x = f ((x-a)/l,b+beta*((x-a)/l)) := rfl

theorem planarCarrier_temperate (a cy delta frequency y : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ =>
      Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)) := by
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

def modulatedPlanarSlice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ =>
    Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I))
    (scaledPlanarSlice f a l ((y-cy)/W) (delta*l/W) hl)

theorem modulatedPlanarSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    modulatedPlanarSlice f a cy l W delta frequency y hl x =
      Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)*
        f ((x-a)/l,(y-cy+delta*(x-a))/W) := by
  rw [modulatedPlanarSlice, SchwartzMap.smulLeftCLM_apply_apply
    (planarCarrier_temperate a cy delta frequency y), scaledPlanarSlice_apply]
  simp only [smul_eq_mul]
  congr 2
  congr 1
  field_simp

theorem modulatedPlanarSlice_norm (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    ‖modulatedPlanarSlice f a cy l W delta frequency y hl x‖ =
      ‖f ((x-a)/l,(y-cy+delta*(x-a))/W)‖ := by
  rw [modulatedPlanarSlice_apply, norm_mul]
  have he : ‖Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [he, one_mul]

theorem modulatedPlanarSlice_vertical_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => modulatedPlanarSlice f a cy l W delta frequency t hl x)
      (((frequency:ℂ)*Complex.I)*modulatedPlanarSlice f a cy l W delta frequency y hl x +
        Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)*
          ((1/W:ℝ):ℂ)*planarVerticalDerivative f ((x-a)/l,(y-cy+delta*(x-a))/W)) y := by
  have hg : HasDerivAt (fun t : ℝ => ((x-a)/l,(t-cy+delta*(x-a))/W)) (0,1/W) y := by
    simpa only [sub_zero, add_zero, one_div, id_eq] using (hasDerivAt_const y ((x-a)/l)).prodMk
      ((((hasDerivAt_id y).sub_const cy).add_const (delta*(x-a))).div_const W)
  have hf := (f.hasFDerivAt ((x-a)/l,(y-cy+delta*(x-a))/W)).comp_hasDerivAt y hg
  have hc := (((((hasDerivAt_id y).sub_const cy).add_const
    (delta*(x-a))).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  have h := hc.mul hf
  convert h using 1
  · funext t
    exact modulatedPlanarSlice_apply f a cy l W delta frequency t hl x
  · rw [modulatedPlanarSlice_apply, planarVerticalDerivative_apply]
    have hv : (0,1/W) = (1/W:ℝ) • ((0,1):ℝ × ℝ) := by simp
    rw [hv, map_smul]
    simp only [Complex.real_smul, Function.comp_apply, id_eq]
    push_cast
    ring

theorem modulatedPlanarSlice_covariant (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarSlice f a cy l W delta frequency t hl x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl x) =
      modulatedPlanarSlice (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
        a cy l W delta frequency y hl x := by
  rw [(modulatedPlanarSlice_vertical_hasDerivAt f a cy l W delta frequency y hl x).deriv]
  simp only [modulatedPlanarSlice_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

end LipschitzHilbert

end

end OAI
