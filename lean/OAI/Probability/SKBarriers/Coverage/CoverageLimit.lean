import Mathlib
import OAI.Probability.SKBarriers.Coverage.EnergyTailGap
import OAI.Probability.SKBarriers.Coverage.CoverageParameters

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem uniform_coverage_pair {β : ℝ} (hβ : 1 < β) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₂ : ℝ, 0 < D₂ ∧
      Tendsto (fun n => (disorderLaw n).real
        (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q))
        atTop (𝓝 0) := by
  obtain ⟨e,he,cE,hcE,N₀,hN₀⟩ := coverage_energy_tail hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  obtain ⟨q,hq,hq1,hK⟩ := exists_positive_coverageGainRate hβpos he.2
  refine ⟨q,hq,hq1,?_⟩
  intro D hD
  obtain ⟨M,D₂,hM,hD₂,hpars⟩ := coverage_eventually_parameters (e := e) (q := q) L hβpos hcE hD hK hL hsub
  refine ⟨D₂,hD₂,?_⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q) ≤
        Real.exp (-cE*(n:ℝ))+2*Real.exp (-L n/(β^2*M)) := by
    filter_upwards [hpars,eventually_ge_atTop N₀] with n hn hlarge
    obtain ⟨hnpos,hLn,hb,htrim,hsecond,hgain⟩ := hn
    have HH := coveragePairBad_probability_le hnpos hβpos.le
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hq.le hb htrim hLn.le hsecond hgain
    have HE := hN₀ n hlarge
    have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
    have hθ : coverageAngle L M n^2 = M*L n/(n:ℝ) := Real.sq_sqrt (by positivity)
    have hquot : -(L n)^2/((coverageAngle L M n)^2*β^2*(n:ℝ)) = -L n/(β^2*M) := by
      rw [hθ]
      field_simp
    rw [hquot] at HH
    exact HH.trans (add_le_add HE le_rfl)
  have hE : Tendsto (fun n : ℕ => Real.exp (-cE*(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (neg_neg_of_pos hcE))
  have hR : Tendsto (fun n => Real.exp (-L n/(β^2*M))) atTop (𝓝 0) := by
    have H := Real.tendsto_exp_atBot.comp
      (hL.const_mul_atTop_of_neg (neg_lt_zero.mpr (show 0 < 1/(β^2*M) by positivity)))
    convert H using 1
    funext n
    congr 1
    ring
  have H := hE.add (hR.const_mul 2)
  simp only [mul_zero,add_zero] at H
  exact squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hbound H

end SK.Analytic

end
end

end

end OAI
