import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageGainRate

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem coverage_eventually_parameters (L : ℕ → ℝ) {β e q cE D : ℝ}
    (hβ : 0 < β) (hcE : 0 < cE) (hD : 0 < D)
    (hK : 0 < coverageGainRate β e q)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ M D₂ : ℝ, 0 < M ∧ 0 < D₂ ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < L n ∧ β*Real.sin (coverageAngle L M n) ≠ 0 ∧
      Real.exp (-cE*(n:ℝ)) ≤ Real.exp (-D*L n)/2 ∧
      4*Real.exp (-D₂*L n)*Real.exp ((β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2) ≤
        Real.exp ((β*Real.sin (coverageAngle L M n))^2*(n:ℝ)*q^2/2) ∧
      L n ≤ Real.log (Real.exp (-D*L n)/2)+
        β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e+
        freshCoverageGain n (β*Real.sin (coverageAngle L M n)) q := by
  let M := (D+2)/coverageGainRate β e q
  have hM : 0 < M := by dsimp only [M]; positivity
  let D₂ := β^2*M+2
  have hD₂ : 0 < D₂ := by dsimp only [D₂]; positivity
  have hMG : M*coverageGainRate β e q-D = 2 := by dsimp only [M]; field_simp; ring
  have hgain := coverage_totalGain_div_tendsto (β := β) (e := e) (D := D) (q := q)
    L hM hL hsub
  rw [hMG] at hgain
  have hsmall : Tendsto (fun n : ℕ => D*(L n/(n:ℝ))+Real.log 2/(n:ℝ))
      atTop (𝓝 0) := by
    have H := (hsub.const_mul D).add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (Real.log 2))
    simpa using H
  refine ⟨M,D₂,hM,hD₂,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ),hL.eventually (eventually_gt_atTop (0:ℝ)),
    hL.eventually (eventually_ge_atTop (Real.log 4)),
    (coverageAngle_tendsto L M hsub).eventually (eventually_lt_nhds Real.pi_pos),
    hsmall.eventually (eventually_lt_nhds hcE),
    (coverageAngle_variance_tendsto (β := β) L hM hL hsub).eventually
      (eventually_lt_nhds (show β^2*M < β^2*M+1 by linarith)),
    hgain.eventually (eventually_gt_nhds (by norm_num : (1:ℝ) < 2))]
    with n hn hLn hLlog hθ htail hV hG
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθpos := coverageAngle_pos hM hn hLn
  have hb : β*Real.sin (coverageAngle L M n) ≠ 0 :=
    ne_of_gt (mul_pos hβ (Real.sin_pos_of_pos_of_lt_pi hθpos hθ))
  refine ⟨hn,hLn,hb,?_,?_,?_⟩
  · have H : D*L n+Real.log 2 < cE*(n:ℝ) := by
      have HH := (div_lt_iff₀ hn').mp (show (D*L n+Real.log 2)/(n:ℝ) < cE by
        simpa only [add_div,mul_div_assoc] using htail)
      exact HH
    rw [show Real.exp (-D*L n)/2 = Real.exp (-D*L n-Real.log 2) by
      rw [Real.exp_sub,Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith
  · have HV : (β*Real.sin (coverageAngle L M n))^2*(n:ℝ) < (β^2*M+1)*L n :=
      (div_lt_iff₀ hLn).mp hV
    have hML : 0 ≤ β^2*M*L n := by positivity
    have HE : Real.log 4-D₂*L n+(β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2 ≤ 0 := by
      dsimp only [D₂]
      nlinarith
    calc
      _ = Real.exp (Real.log 4-D₂*L n+(β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2) := by
        rw [Real.exp_add,Real.exp_sub,Real.exp_log (by norm_num),neg_mul,Real.exp_neg]
        ring
      _ ≤ 1 := (Real.exp_le_one_iff).mpr HE
      _ ≤ _ := Real.one_le_exp (by positivity)
  · simpa only [one_mul] using ((le_div_iff₀ hLn).mp hG.le)

end SK.Analytic

end
end

end

end OAI
