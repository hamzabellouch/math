import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonWindow

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentHeckeWindowEnergy
open CenteredMomentExceptionalAmplitudePair CenteredMomentAllocatedDetectorAmplitude
universe u

theorem heightCost_phase (t θ:ℝ):
    heightCost t θ≤(1+‖t‖)*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have ht:0≤‖t‖:=norm_nonneg t
  have hθ:0≤‖θ‖:=norm_nonneg θ
  have hh:1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖)*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc ht,mul_nonneg ht hθ,mul_nonneg (mul_nonneg hc ht) hθ]
  exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by ring)

theorem mass_phase {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(w:ℝ)(J:ℕ):
    mass R s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass R s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (heightCost_pos s.t w).le (heightCost_phase s.t w) J
  have hq:=pow_le_pow_left₀ (heightCost_pos v.t (-w)).le (heightCost_phase v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (heightCost_pos v.t (-w)).le _) (by positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)))
      (slotControl_nonneg s.toData)) (slotControl_nonneg v.toData))
      (Real.sqrt_nonneg (volume s.toData))) (Real.sqrt_nonneg (volume v.toData))
  have hmass:mass R s v p q s.t v.t w (-w) J =
      p.control R*q.control R*(heightCost s.t w^J*heightCost v.t (-w)^J)*
        slotControl s.toData*slotControl v.toData*Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData):=by
    unfold mass
    ring
  rw [hmass]
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
