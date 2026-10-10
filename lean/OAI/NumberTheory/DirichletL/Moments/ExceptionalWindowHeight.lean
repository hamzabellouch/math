import OAI.NumberTheory.DirichletL.Moments.ExceptionalHeight

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalWindowHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentExceptionalHeight
open CenteredMomentHeckeWindowEnergy CenteredMomentAllocatedDetectorAmplitude
universe u

theorem cost_phase (p:Tests)(t θ:ℝ):
    cost p t θ≤p.heightWeight t*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have hp:1≤p.heightWeight t:=by
    dsimp only [Tests.heightWeight]
    linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),norm_nonneg t]
  have h1:cost p t θ≤(p.heightWeight t+2*Real.pi*‖θ‖)*(1+2*Real.pi):=by
    dsimp only [cost,Tests.heightWeight,heightCost]
    nlinarith [mul_nonneg hc (norm_nonneg (p.height 0)),mul_nonneg hc (norm_nonneg (p.height 1))]
  have h2:p.heightWeight t+2*Real.pi*‖θ‖≤p.heightWeight t*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc (norm_nonneg θ),mul_nonneg hc (show 0≤p.heightWeight t by linarith),
      mul_nonneg (show 0≤p.heightWeight t-1 by linarith) (mul_nonneg hc (norm_nonneg θ)),
      mul_nonneg (show 0≤p.heightWeight t by linarith) (norm_nonneg θ)]
  exact h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans_eq (by ring))

theorem mass_phase {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(w:ℝ)(J:ℕ):
    mass s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (cost_pos p s.t w).le (cost_phase p s.t w) J
  have hq:=pow_le_pow_left₀ (cost_pos q v.t (-w)).le (cost_phase q v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (cost_pos q v.t (-w)).le _) (by dsimp only [Tests.heightWeight]; positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
        (Real.sqrt_nonneg (volume v.toData))
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring

end SevenEighths.CenteredMomentExceptionalWindowHeight

end

end OAI
