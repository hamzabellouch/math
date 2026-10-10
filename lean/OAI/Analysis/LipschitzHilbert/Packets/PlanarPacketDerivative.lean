import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketEnvelope

namespace OAI

/-! Horizontal derivatives of general modulated packets. Uniform bounds
use precisely the dimensionless carrier and slope restrictions. -/

noncomputable section
namespace LipschitzHilbert

def planarHorizontalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.evalCLM ℂ (ℝ × ℝ) ℂ (1,0) (SchwartzMap.fderivCLM ℂ (ℝ × ℝ) ℂ f)

@[simp] theorem planarHorizontalDerivative_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (z : ℝ × ℝ) :
    planarHorizontalDerivative f z = fderiv ℝ f z (1,0) := rfl

theorem modulatedPlanarSlice_horizontal_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    HasDerivAt (modulatedPlanarSlice f a cy l W delta frequency y hl)
      (((frequency*delta:ℝ):ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl x +
        ((1/l:ℝ):ℂ)*modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl x +
        ((delta/W:ℝ):ℂ)*modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl x) x := by
  have hg : HasDerivAt (fun t : ℝ => ((t-a)/l,(y-cy+delta*(t-a))/W)) (1/l,delta/W) x := by
    simpa only [id_eq, mul_one, zero_add] using
      (((hasDerivAt_id x).sub_const a).div_const l).prodMk
      ((((hasDerivAt_id x).sub_const a).const_mul delta).const_add (y-cy) |>.div_const W)
  have hf := (f.hasFDerivAt ((x-a)/l,(y-cy+delta*(x-a))/W)).comp_hasDerivAt x hg
  have hc := ((((((hasDerivAt_id x).sub_const a).const_mul delta).const_add
    (y-cy)).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  have h := hc.mul hf
  convert h using 1
  · funext t
    exact modulatedPlanarSlice_apply f a cy l W delta frequency y hl t
  · simp only [modulatedPlanarSlice_apply,planarHorizontalDerivative_apply,
      planarVerticalDerivative_apply,Function.comp_apply,id_eq]
    have hv : (1/l,delta/W) = (1/l:ℝ) • ((1,0):ℝ × ℝ) + (delta/W:ℝ) • ((0,1):ℝ × ℝ) := by
      ext <;> simp
    rw [hv, map_add, map_smul, map_smul]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem modulatedPlanarSlice_derivative_bound (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y C M : ℝ) (hl : 0 < l) (n : ℕ)
    (hC : 0 ≤ C) (hshear : |delta*l/W| ≤ 1) (hcarrier : |frequency*delta*l| ≤ M)
    (hf : ∀ z, ‖f z‖ ≤ C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (hx : ∀ z, ‖planarHorizontalDerivative f z‖ ≤
      C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (hy : ∀ z, ‖planarVerticalDerivative f z‖ ≤
      C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2)) (x : ℝ) :
    ‖deriv (modulatedPlanarSlice f a cy l W delta frequency y hl.ne') x‖ ≤
      ((M+2)*2^n*C/l)*(lineEnvelope a l n x*lineEnvelope cy W n y) := by
  let E := lineEnvelope a l n x*lineEnvelope cy W n y
  have hE : 0 ≤ E := mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hb := modulatedPlanarSlice_envelope f a cy l W delta frequency y C hl.ne' n hC hshear hf x
  have hbx := modulatedPlanarSlice_envelope (planarHorizontalDerivative f)
    a cy l W delta frequency y C hl.ne' n hC hshear hx x
  have hby := modulatedPlanarSlice_envelope (planarVerticalDerivative f)
    a cy l W delta frequency y C hl.ne' n hC hshear hy x
  have hM : 0 ≤ M := (abs_nonneg _).trans hcarrier
  have hc : |frequency*delta| ≤ M/l := by
    apply (le_div_iff₀ hl).mpr
    simpa only [abs_mul, abs_of_pos hl, mul_assoc] using hcarrier
  have hs : |delta/W| ≤ 1/l := by
    apply (le_div_iff₀ hl).mpr
    have heq : |delta/W| * l = |delta*l/W| := by
      simp only [abs_div, abs_mul, abs_of_pos hl]
      ring
    rw [heq]
    exact hshear
  rw [(modulatedPlanarSlice_horizontal_hasDerivAt f a cy l W delta frequency y hl.ne' x).deriv]
  calc
    _ ≤ ‖((frequency*delta:ℝ):ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl.ne' x‖ +
        ‖((1/l:ℝ):ℂ)*modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl.ne' x‖ +
        ‖((delta/W:ℝ):ℂ)*modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl.ne' x‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = |frequency*delta| * ‖modulatedPlanarSlice f a cy l W delta frequency y hl.ne' x‖ +
        (1/l)*‖modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl.ne' x‖ +
        |delta/W| * ‖modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl.ne' x‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul,
        abs_of_pos (one_div_pos.mpr hl), abs_mul, mul_assoc]
    _ ≤ (M/l)*((2^n*C)*E)+(1/l)*((2^n*C)*E)+(1/l)*((2^n*C)*E) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul hc hb (norm_nonneg _) (div_nonneg hM hl.le))
          (mul_le_mul_of_nonneg_left hbx (by positivity))
      · exact mul_le_mul hs hby (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [E]; ring

end LipschitzHilbert

end

end OAI
