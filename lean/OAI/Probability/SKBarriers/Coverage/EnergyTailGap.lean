import Mathlib
import OAI.Probability.SKBarriers.Coverage.FiniteTemperatureBound
import OAI.Probability.SKBarriers.Coverage.EnergyTail

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem coverage_energy_tail {β : ℝ} (hβ : 1 < β) :
    ∃ e₁ : ℝ, e₁ ∈ Set.Ioo 0 (β/2) ∧ ∃ cE : ℝ, 0 < cE ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (disorderLaw N).real {J | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ≤
          Real.exp (-cE*(N:ℝ)) := by
  obtain ⟨γ,hβγ,hsec⟩ := exists_strict_finiteParisiInf_secant hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hγpos : 0 < γ := hβpos.trans hβγ
  have hd : 0 < γ-β := sub_pos.mpr hβγ
  let L := (finiteParisiInf γ-finiteParisiInf β)/(γ-β)
  obtain ⟨e₁,he₁low,he₁high⟩ := exists_between
    (show max 0 L < β/2 from max_lt (by positivity) hsec)
  have he₁pos : 0 < e₁ := lt_of_le_of_lt (le_max_left 0 L) he₁low
  have hLe : L < e₁ := lt_of_le_of_lt (le_max_right 0 L) he₁low
  let a := (γ-β)*(e₁-L)/6
  have ha : 0 < a := by dsimp only [a]; positivity
  let r := 4*a^2/(Real.pi^2*γ^2)
  have hr : 0 < r := by dsimp only [r]; positivity
  let cE := min a (r/2)
  have hcE : 0 < cE := lt_min ha (by positivity)
  have hca : cE ≤ a := min_le_left _ _
  have hcr : 2*cE ≤ r := by dsimp only [cE]; linarith [min_le_right a (r/2)]
  have Hlim : Tendsto (fun N : ℕ => quenchedPressure γ N-quenchedPressure β N)
      atTop (𝓝 (finiteParisiInf γ-finiteParisiInf β)) :=
    (quenchedPressure_tendsto_finiteParisiInf hγpos).sub
      (quenchedPressure_tendsto_finiteParisiInf hβpos)
  have hlim : finiteParisiInf γ-finiteParisiInf β < (γ-β)*e₁-3*a := by
    have hL : (γ-β)*L = finiteParisiInf γ-finiteParisiInf β := by
      dsimp only [L]; field_simp
    dsimp only [a]
    nlinarith [mul_pos hd (sub_pos.mpr hLe)]
  have HP := Hlim.eventually (eventually_lt_nhds hlim)
  have HN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (Real.log 2/cE))
  have HE : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N).real {J | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ≤
        Real.exp (-cE*(N:ℝ)) := by
    filter_upwards [HP,HN,eventually_gt_atTop (0:ℕ)] with N hP hN hNpos
    have hn : (0:ℝ) ≤ N := by positivity
    have hsub : {J : Disorder N | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ⊆
        {J | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e₁ J} := by
      intro J hJ
      exact lt_of_le_of_lt (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hca) hn)) hJ
    have HM := (measureReal_mono hsub).trans
      (gibbsEnergyTail_probability_le hNpos hβpos hβγ ha hP.le)
    have hlog : Real.log 2 ≤ cE*(N:ℝ) := by
      have HH := (div_le_iff₀ hcE).mp hN
      nlinarith
    have hrate : 2*cE*(N:ℝ) ≤ r*(N:ℝ) := mul_le_mul_of_nonneg_right hcr hn
    apply HM.trans
    change 2*Real.exp (-r*(N:ℝ)) ≤ Real.exp (-cE*(N:ℝ))
    rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp HE
  exact ⟨e₁,⟨he₁pos,he₁high⟩,cE,hcE,N₀,hN₀⟩
end SK.Analytic

end
end

end

end OAI
