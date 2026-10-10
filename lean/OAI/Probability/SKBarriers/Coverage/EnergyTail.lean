import Mathlib
import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def gibbsEnergyTail {N : ℕ} (β e : ℝ) (J : Disorder N) : ℝ :=
  ∑ s : Config N, if (N:ℝ)*e < hamiltonian J s then gibbs β J s else 0

theorem gibbsEnergyTail_le {N : ℕ} {β γ : ℝ} (hβγ : β < γ)
    (e : ℝ) (J : Disorder N) :
    gibbsEnergyTail β e J ≤
      Real.exp (logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e) := by
  have hZβ := partition_pos β J
  have hZγ := partition_pos γ J
  have he : Real.exp (logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e) =
      Real.exp (-((γ-β)*(N:ℝ)*e))*partition γ J/partition β J := by
    rw [show logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e =
      -((γ-β)*(N:ℝ)*e)+(logPartition γ J-logPartition β J) by ring,
      Real.exp_add,Real.exp_sub]
    simp only [logPartition,Real.exp_log hZγ,Real.exp_log hZβ]
    ring
  rw [he]
  unfold gibbsEnergyTail
  calc
    _ ≤ ∑ s : Config N,
        Real.exp (-((γ-β)*(N:ℝ)*e))*Real.exp (γ*hamiltonian J s)/partition β J := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs with hs
      · unfold gibbs
        apply div_le_div_of_nonneg_right _ hZβ.le
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have H := mul_le_mul_of_nonneg_left hs.le (sub_pos.mpr hβγ).le
        nlinarith
      · positivity
    _ = _ := by rw [← Finset.sum_div,← Finset.mul_sum]; rfl

theorem logPartition_upper_tail_linear {N : ℕ} (hN : 0 < N) {β a : ℝ}
    (hβ : β ≠ 0) (ha : 0 ≤ a) :
    (disorderLaw N).real {J | a*(N:ℝ) ≤ logPartition β J-
      ∫ K, logPartition β K ∂disorderLaw N} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2))*(N:ℝ)) := by
  have H := logPartition_upper_tail hN β (a*(N:ℝ)) (by positivity)
  convert H using 1
  congr 1
  change -(4*a^2/(Real.pi^2*β^2))*(N:ℝ) =
    -(a*(N:ℝ))^2/(2*(Real.pi^2*β^2*(N:ℝ)/8))
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem logPartition_lower_tail_linear {N : ℕ} (hN : 0 < N) {β a : ℝ}
    (hβ : β ≠ 0) (ha : 0 ≤ a) :
    (disorderLaw N).real {J | a*(N:ℝ) ≤
      (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2))*(N:ℝ)) := by
  have H := logPartition_lower_tail hN β (a*(N:ℝ)) (by positivity)
  convert H using 1
  congr 1
  change -(4*a^2/(Real.pi^2*β^2))*(N:ℝ) =
    -(a*(N:ℝ))^2/(2*(Real.pi^2*β^2*(N:ℝ)/8))
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem gibbsEnergyTail_probability_le {N : ℕ} (hN : 0 < N) {β γ e a : ℝ}
    (hβ : 0 < β) (hβγ : β < γ) (ha : 0 < a)
    (hP : quenchedPressure γ N-quenchedPressure β N ≤ (γ-β)*e-3*a) :
    (disorderLaw N).real {J | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e J} ≤
      2*Real.exp (-(4*a^2/(Real.pi^2*γ^2))*(N:ℝ)) := by
  let A := {J : Disorder N | a*(N:ℝ) ≤ logPartition γ J-
    ∫ K, logPartition γ K ∂disorderLaw N}
  let B := {J : Disorder N | a*(N:ℝ) ≤
    (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J}
  have hsub : {J : Disorder N | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e J} ⊆ A ∪ B := by
    intro J hJ
    by_contra hbad
    have hA : logPartition γ J-(∫ K, logPartition γ K ∂disorderLaw N) < a*(N:ℝ) :=
      lt_of_not_ge (fun h => hbad (Or.inl h))
    have hB : (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J < a*(N:ℝ) :=
      lt_of_not_ge (fun h => hbad (Or.inr h))
    have hPlin := mul_le_mul_of_nonneg_right hP (show (0:ℝ) ≤ N by positivity)
    have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [quenchedPressure,sub_mul,div_mul_cancel₀ _ hNne] at hPlin
    have hbound := gibbsEnergyTail_le hβγ e J
    have hsmall : logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e ≤ -a*(N:ℝ) := by
      nlinarith
    exact (not_lt_of_ge (hbound.trans (Real.exp_le_exp.mpr hsmall))) hJ
  have hγ : 0 < γ := hβ.trans hβγ
  have Hγ := logPartition_upper_tail_linear hN hγ.ne' ha.le
  have Hβ := logPartition_lower_tail_linear hN hβ.ne' ha.le
  have hrate : 4*a^2/(Real.pi^2*γ^2) ≤ 4*a^2/(Real.pi^2*β^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
    nlinarith
  have Hβ' : (disorderLaw N).real B ≤
      Real.exp (-(4*a^2/(Real.pi^2*γ^2))*(N:ℝ)) := by
    apply Hβ.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hrate) (by positivity)
  exact (measureReal_mono hsub).trans ((measureReal_union_le A B).trans (by linarith))
end SK.Analytic

end
end

end

end OAI
