import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth

namespace OAI

/-! Every actual primitive row height, with arbitrary complex power,
satisfies the hyperbolic spectral equation. This removes the nonzero
cubic phase from the already proved literal grid equation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGridTerm_row_height (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (r.c,r.d) p s=
      star r.phase*(r.height p:ℂ)^s := by
  have hr : cubicThetaAdmissiblePair (r.c,r.d) := ⟨r.c_three,r.d_primary,r.coprime⟩
  simp only [cubicThetaEisensteinGridTerm,hr,ite_true,CubicThetaBottomRow.phase,
    star_star,CubicThetaBottomRow.height]

lemma cubicThetaHyperbolicOperator_const_mul (F : ℝ → ℝ → ℝ → ℂ)
    (c : ℂ) (x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun a b t => c*F a b t) x y v=
      c*cubicThetaHyperbolicOperator F x y v := by
  simpa only [add_zero] using cubicThetaHyperbolicOperator_translate F c 0 0 x y v

theorem cubicThetaRowHeightPower_eigenvalue (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => (r.height (cubicThetaCartesianPoint a b t):ℂ)^s) x y v=
      s*(s-2)*(r.height (cubicThetaCartesianPoint x y v):ℂ)^s := by
  have h := cubicThetaEisensteinGrid_eigenvalue r.c r.d s x y hv
  simp_rw [cubicThetaGridTerm_row_height r] at h
  rw [cubicThetaHyperbolicOperator_const_mul] at h
  have hn : star r.phase≠0 := by
    intro hz
    have hnorm : ‖star r.phase‖=1 := by rw [norm_star,r.phase_norm]
    rw [hz,norm_zero] at hnorm
    exact zero_ne_one hnorm
  apply mul_left_cancel₀ hn
  calc
    _ = s*(s-2)*(star r.phase*(r.height (cubicThetaCartesianPoint x y v):ℂ)^s) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
