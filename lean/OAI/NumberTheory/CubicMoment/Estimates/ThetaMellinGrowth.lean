import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! A quadratic exponential growth bound derived from theta decay and inversion. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma theta_mellin_growth {f g : ℝ → ℂ} {ε : ℂ} {C D c : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfcont : ContinuousOn f (Ioi 0)) (hgcont : ContinuousOn g (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖g t‖ ≤ D*Real.exp (-c*t))
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖mellin f s‖ ≤ Real.exp (B*(1+‖s‖)^2) := by
  let K := 2*C/c+‖ε‖*(2*D/c)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+8/c,by positivity,?_⟩
  intro s
  have hf' := thetaUpper_mellinConvergent hc hfcont hf s
  have hg' := thetaUpper_mellinConvergent hc hgcont hg (1-s)
  have hsplit := theta_mellin_split hFE hf' hg'
  have hfb := theta_upper_norm_bound hc hf s
  have hgb := theta_upper_norm_bound hc hg (1-s)
  have hn : 1+‖1-s‖ ≤ 2*(1+‖s‖) := by
    have hh := norm_sub_le (1:ℂ) s
    rw [norm_one] at hh
    linarith [_root_.norm_nonneg s]
  have hnsq : (1+‖1-s‖)^2 ≤ 4*(1+‖s‖)^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 1+‖1-s‖ by positivity) hn 2
    nlinarith
  have hexp : Real.exp (2*(1+‖1-s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖1-s‖)^2 ≤ 8*(1+‖s‖)^2 := by linarith
    convert div_le_div_of_nonneg_right hh hc.le using 1
    ring
  have hexp' : Real.exp (2*(1+‖s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖s‖)^2 ≤ 8*(1+‖s‖)^2 := by nlinarith [sq_nonneg (1+‖s‖)]
    convert div_le_div_of_nonneg_right hh hc.le using 1
    ring
  calc
    ‖mellin f s‖ ≤ ‖mellin (thetaUpper f) s‖+‖ε*mellin (thetaUpper g) (1-s)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = ‖mellin (thetaUpper f) s‖+‖ε‖*‖mellin (thetaUpper g) (1-s)‖ := by rw [norm_mul]
    _ ≤ (2*C/c)*Real.exp (2*(1+‖s‖)^2/c)+
        ‖ε‖*((2*D/c)*Real.exp (2*(1+‖1-s‖)^2/c)) := by
      rw [mellin_thetaUpper,mellin_thetaUpper]
      exact add_le_add hfb (mul_le_mul_of_nonneg_left hgb (_root_.norm_nonneg ε))
    _ ≤ K*Real.exp ((8/c)*(1+‖s‖)^2) := by
      calc
        _ ≤ (2*C/c)*Real.exp ((8/c)*(1+‖s‖)^2)+
            ‖ε‖*((2*D/c)*Real.exp ((8/c)*(1+‖s‖)^2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp' (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity))
              (_root_.norm_nonneg ε))
        _ = _ := by dsimp [K]; ring
    _ ≤ Real.exp K*Real.exp ((8/c)*(1+‖s‖)^2) :=
      mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp K)) (Real.exp_pos _).le
    _ ≤ Real.exp ((K+8/c)*(1+‖s‖)^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hq : 1 ≤ (1+‖s‖)^2 := one_le_pow₀ (by linarith [_root_.norm_nonneg s])
      nlinarith

lemma idealThetaFEPair_finiteOrder {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
    CompletedHeckeFiniteOrder A (thetaHeckeL A P.Λ) := by
  dsimp only
  let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
  have hP := idealThetaFEPair_strong hA χ χdual hχ hχdual hε hFE
  let C := ∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A))
  have hC : 0 ≤ C := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hbound (ψ : EisensteinIdealExponent → ℂ) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
      (t : ℝ) (ht : 1 ≤ t) :
      ‖idealTheta A ψ t‖ ≤ C*Real.exp (-(1/(2*A))*t) := by
    have he : -(1/(2*A))*t = -t/(2*A) := by ring
    simpa only [he] using idealTheta_norm_bound hA ψ hψ ht
  obtain ⟨B,hB,hBbound⟩ := theta_mellin_growth (show 0 < 1/(2*A) by positivity)
    hC hC (idealTheta_continuousOn hA χ hχ) (idealTheta_continuousOn hA χdual hχdual)
    (hbound χ hχ) (hbound χdual hχdual) hFE
  apply thetaHeckeL_finiteOrder hA hP.differentiable_Λ hB
  intro s
  rw [hP.Λ_eq]
  exact hBbound s

end CubicFirstMoment

end

end OAI
