import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageAsymptotic
import OAI.Probability.SKBarriers.Coverage.CoverageAngle

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def coverageGainRate (β e q : ℝ) : ℝ :=
  β^2/4-β*e/2-Real.sqrt (Real.pi^2*(β^2)^2*q^2/8)

theorem exists_positive_coverageGainRate {β e : ℝ} (hβ : 0 < β) (he : e < β/2) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ 0 < coverageGainRate β e q := by
  let g := β^2/4-β*e/2
  have hg : 0 < g := by dsimp only [g]; nlinarith
  let q := min (1/2:ℝ) (g/(4*Real.pi*β^2))
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hq1 : q < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hqbound : Real.pi*β^2*q ≤ g/4 := by
    have H := (le_div_iff₀ (show 0 < 4*Real.pi*β^2 by positivity)).mp (min_le_right (1/2:ℝ) (g/(4*Real.pi*β^2)))
    change q*(4*Real.pi*β^2) ≤ g at H
    nlinarith
  have hroot : Real.sqrt (Real.pi^2*(β^2)^2*q^2/8) ≤ Real.pi*β^2*q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have H : 0 ≤ (Real.pi*β^2*q)^2 := sq_nonneg _
      nlinarith
  refine ⟨q,hq,hq1,?_⟩
  change 0 < g-Real.sqrt (Real.pi^2*(β^2)^2*q^2/8)
  linarith

theorem coverage_totalGain_div_tendsto (L : ℕ → ℝ) {M β e D q : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (Real.log (Real.exp (-D*L n)/2)+
      β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e+
      freshCoverageGain n (β*Real.sin (coverageAngle L M n)) q)/L n)
      atTop (𝓝 (M*coverageGainRate β e q-D)) := by
  have hlog : Tendsto (fun n => Real.log (Real.exp (-D*L n)/2)/L n) atTop (𝓝 (-D)) := by
    have H := (tendsto_const_nhds (x := -D)).sub (hL.const_div_atTop (Real.log 2))
    simp only [sub_zero] at H
    apply H.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with n hLn
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp]
    field_simp
  have hV := coverageAngle_variance_tendsto (β := β) L hM hL hsub
  have hf := freshCoverageGain_div_tendsto (q := q) L
    (fun n => β*Real.sin (coverageAngle L M n)) hL hV
  have he' := coverageAngle_loss_tendsto (β := β) (e := e) L hM hL hsub
  have H := (hlog.add he').add hf
  have hroot : Real.sqrt (Real.pi^2*(β^2*M)^2*q^2/8) =
      M*Real.sqrt (Real.pi^2*(β^2)^2*q^2/8) := by
    rw [show Real.pi^2*(β^2*M)^2*q^2/8 = M^2*(Real.pi^2*(β^2)^2*q^2/8) by ring,
      Real.sqrt_mul (sq_nonneg M),Real.sqrt_sq_eq_abs,abs_of_pos hM]
  convert H using 1
  · funext n
    rw [add_div,add_div]
  · rw [hroot]
    unfold coverageGainRate
    congr 1
    ring

end SK.Analytic

end
end

end

end OAI
