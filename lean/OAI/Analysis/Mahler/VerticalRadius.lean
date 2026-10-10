import OAI.Analysis.Mahler.ConformalInverse

namespace OAI

/-! Vertical geometry of the actual inverse. The squared inverse radius has
positive vertical derivative on the image of the upper half-disk. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def verticalRadiusSq (q ξ : ℝ) : ℝ := Complex.normSq (inverseF ((q : ℂ)+ξ*I))

lemma hasDerivAt_normSq {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => Complex.normSq (f x))
      (2*((f t).re*f'.re+(f t).im*f'.im)) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hre.mul hre).add (him.mul him) using 1 <;> (try rfl)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_apply]
  ring

lemma im_polar_mul_deriv_F {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (polar r θ * deriv F (polar r θ)).im = B r θ := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  rw [(hasDerivAt_F_log hw (polar_ne_zero hr θ)).deriv]
  have he : polar r θ * (4/((Real.pi : ℂ)^2*polar r θ)*Complex.log (cayley (polar r θ))) =
      ((4/Real.pi^2 : ℝ) : ℂ)*Complex.log (cayley (polar r θ)) := by
    push_cast
    field_simp [polar_ne_zero hr θ]
  change (polar r θ * (4/((Real.pi : ℂ)^2*polar r θ)*Complex.log (cayley (polar r θ)))).im = _
  rw [he, Complex.im_ofReal_mul, Complex.log_im, arg_cayley_polar hr hr1]
  rfl

/-- Differentiation in the actual vertical coordinate of Omega. -/
theorem hasDerivAt_verticalRadiusSq {q ξ : ℝ} (hu : (q : ℂ)+ξ*I ∈ Omega) :
    HasDerivAt (verticalRadiusSq q)
      (2*(inverseF ((q : ℂ)+ξ*I)*deriv F (inverseF ((q : ℂ)+ξ*I))).im /
        ‖deriv F (inverseF ((q : ℂ)+ξ*I))‖^2) ξ := by
  let w := inverseF ((q : ℂ)+ξ*I)
  let d := deriv F w
  have hl : HasDerivAt (fun z : ℂ => (q : ℂ)+z*I) I (ξ : ℂ) := by
    simpa using ((hasDerivAt_id (ξ : ℂ)).mul_const I).const_add (q : ℂ)
  have hf := ((hasDerivAt_inverseF hu).comp (ξ : ℂ) hl).comp_ofReal
  have hd : d⁻¹*I = I/d := by ring
  change HasDerivAt (fun t : ℝ => inverseF ((q : ℂ)+t*I)) (d⁻¹*I) ξ at hf
  rw [hd] at hf
  have hn := hasDerivAt_normSq hf
  change HasDerivAt (verticalRadiusSq q) (2*(w.re*(I/d).re+w.im*(I/d).im)) ξ at hn
  have he : 2*(w.re*(I/d).re+w.im*(I/d).im) = 2*(w*d).im/‖d‖^2 := by
    simp only [Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_div, zero_add, sub_zero, Complex.mul_im,
      Complex.normSq_eq_norm_sq]
    ring
  rwa [he] at hn

lemma Q_add_S_I (r θ : ℝ) : (Q r θ : ℂ)+(S r θ : ℂ)*I = F (polar r θ) := by
  exact Complex.re_add_im _

/-- At each upper-semicircle image point, the inverse radius increases vertically.
This is the inverse differential form of the vertical-speed identity. -/
theorem hasDerivAt_verticalRadiusSq_polar {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (verticalRadiusSq (Q r θ))
      (2*B r θ/‖deriv F (polar r θ)‖^2) (S r θ) := by
  have hw : polar r θ ∈ ball (0 : ℂ) 1 := by simpa [norm_polar hr.le] using hr1
  have hu : (Q r θ : ℂ)+(S r θ : ℂ)*I ∈ Omega := by
    rw [Q_add_S_I]
    exact ⟨polar r θ, hw, rfl⟩
  have hd := hasDerivAt_verticalRadiusSq hu
  rw [Q_add_S_I, inverseF_left hw, im_polar_mul_deriv_F hr hr1] at hd
  exact hd

theorem verticalRadiusSq_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    verticalRadiusSq (Q r θ) (S r θ) = r^2 := by
  unfold verticalRadiusSq
  rw [Q_add_S_I, inverseF_left (by simpa [norm_polar hr.le] using hr1),
    Complex.normSq_eq_norm_sq, norm_polar hr.le]

theorem verticalRadiusSq_deriv_pos {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    0 < deriv (verticalRadiusSq (Q r θ)) (S r θ) := by
  rw [(hasDerivAt_verticalRadiusSq_polar hr hr1).deriv]
  exact div_pos (mul_pos (by norm_num) (B_pos hr hr1 hθ hθπ))
    (sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (by rwa [norm_polar hr.le]))))

end MahlerConformal

end

end OAI
