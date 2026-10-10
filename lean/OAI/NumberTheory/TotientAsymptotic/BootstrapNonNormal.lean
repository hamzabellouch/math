import OAI.NumberTheory.TotientAsymptotic.DyadicLogGeometry

namespace OAI

/-! The normality exception is small relative to the finite counting envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_non_normal_exception : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ (2:ℝ)^J ∧ ¬IsNormalPrime (loglogCutoff (bootstrapBottom (B ((2:ℝ)^J)))) p) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  obtain ⟨C,hC,hcount⟩ := uniform_non_normal_value_count
  let ε := fun J : ℕ => (C*Real.exp (1/3:ℝ))*
    ((B ((2:ℝ)^J)+2)^6*Real.exp (-B ((2:ℝ)^J)/600000000))
  have hlim : Tendsto ε atTop (nhds 0) := by
    have hh := ((shifted_sixth_exp_decay (by norm_num : (0:ℝ)<1/600000000)).comp dyadic_B_tendsto).const_mul
      (C*Real.exp (1/3:ℝ))
    convert hh using 1
    · funext J
      dsimp only [ε,Function.comp_apply]
      rw [show -(1/600000000:ℝ)*B ((2:ℝ)^J) = -B ((2:ℝ)^J)/600000000 by ring]
    · simp
  refine ⟨ε,hlim,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [dyadic_B_tendsto.eventually (eventually_ge_atTop 300000000),
    hxlim.eventually (eventually_ge_atTop 256),eventually_ge_atTop (1:ℕ)] with J hb hx hJ
  let b := B ((2:ℝ)^J)
  let S := loglogCutoff (bootstrapBottom b)
  have hs := bootstrap_normality_factor hb
  change 2 < (S:ℝ) ∧ 0 ≤ B S ∧ (Real.log S)^(-1/6:ℝ) ≤
    Real.exp (1/3:ℝ)*Real.exp (-b/600000000) at hs
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hpoly := dyadic_normality_polynomial hJ hb0
  have hlog : 0 < Real.log ((2:ℝ)^J) := Real.log_pos (by linarith)
  have hE0 : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  have hcoef : 0 ≤ C*dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J) := by positivity
  have hnorm0 : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg
    (Real.log_pos (by linarith : (1:ℝ)<S)).le _
  have hm := mul_le_mul hpoly hs.2.2 hnorm0 (pow_nonneg (by linarith : 0 ≤ b+2) 6)
  intro Q hQ
  have hh := hcount S ((2:ℝ)^J) J hs.1 hs.2.1 hx hJ le_rfl Q hQ
  have hu := mul_le_mul_of_nonneg_left hm hcoef
  apply hh.trans
  calc
    _ = (C*dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J))*
        ((B (2*(2:ℝ)^J))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ)) := by ring
    _ ≤ _ := hu
    _ = _ := by dsimp [ε,b]; ring

end TotientAsymptotic

end

end OAI
