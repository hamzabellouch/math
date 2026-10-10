import OAI.Dynamics.StandardMap.EntropyParameters

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma integral_log_growth_of_deficit (k:ℝ) (hk:0≤k)
    (hdef:∀n:ℕ,0<n → meanDeficit k n<(1/8:ℝ)) (n:ℕ) :
    (7/8:ℝ)*(n:ℝ)*Real.log (growthBase k)≤∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area := by
  by_cases hn:0<n
  · have hnp:(0:ℝ)<n := by exact_mod_cast hn
    have hl:=log_growthBase_pos k hk
    have hI:(7/8:ℝ)*(n:ℝ)≤∫z,productDistance k z 0 (n:ℤ) ∂area := by
      have hd:=hdef n hn
      unfold meanDeficit at hd
      have hh:(7/8:ℝ)<(∫z,productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) := by linarith
      exact ((lt_div_iff₀ hnp).mp hh).le
    have he:(∫z,productDistance k z 0 (n:ℤ) ∂area)=
        (∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area)/Real.log (growthBase k) := by
      have hf:(fun z=>productDistance k z 0 (n:ℤ))=(fun z=>Real.log ‖torusSegmentTransfer k z 0 n‖/Real.log (growthBase k)) := by
        funext z
        simpa only [zero_add] using productDistance_forward k z 0 n
      rw [hf,integral_div]
    rw [he] at hI
    exact (le_div_iff₀ hl).mp hI
  · have he:n=0 := by omega
    subst n
    simp only [Nat.cast_zero,mul_zero,zero_mul]
    exact integral_nonneg fun z=>Real.log_nonneg (torusSegmentTransfer_norm_bounds k hk z 0 0).1

lemma positive_entropy_of_uniform_deficit (k:ℝ) (hk:0≤k) (hM:(1000:ℝ)^4≤growthBase k)
    (hdef:∀n:ℕ,0<n → meanDeficit k n<(1/8:ℝ)) : 0 < metricEntropy area (standardMap k) := by
  obtain ⟨N,hN,hN2,hNR⟩:=entropy_subdivision_parameters (growthBase k) hM
  obtain ⟨ε,Q,hε,hQ,hε1,hε2,hQε,hQC⟩:=entropy_grid_parameters (growthBase k) (by linarith [growthBase_ge_four k hk])
  have hlog:=log_growthBase_pos k hk
  have hblock (n:ℕ) : ((n:ℝ)+1)*(Real.log (growthBase k)/8)≤
      blockEntropy area (torusStep k) (gridPartition Q hQ) (n+1) := by
    have h:=grid_block_entropy_growth k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n
    have hg:=integral_log_growth_of_deficit k hk hdef n
    have hr:=mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg n : (0:ℝ)≤n)
    nlinarith
  have hp:ENNReal.ofReal (Real.log (growthBase k)/8)≤
      partitionEntropy area (torusStep k) (gridPartition Q hQ) := by
    apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (show (0:ℝ)<(n:ℝ)+1 by positivity)).mpr
    nlinarith [hblock n]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
    (hp.trans (metricEntropy_standardMap_ge_partition k (gridPartition Q hQ)))

theorem main_entropy : MainObligation := by
  obtain ⟨K,hK,hdef⟩:=eventually_meanDeficit_small (1/8:ℝ) (by norm_num)
  refine ⟨max K ((1000:ℝ)^4),lt_of_lt_of_le hK (le_max_left _ _),?_⟩
  intro k hk
  have hKk:K≤k := (le_max_left K ((1000:ℝ)^4)).trans hk
  have hlarge:(1000:ℝ)^4≤k := (le_max_right K ((1000:ℝ)^4)).trans hk
  have hk0:0≤k := le_of_lt (hK.trans_le hKk)
  apply positive_entropy_of_uniform_deficit k hk0
  · unfold growthBase
    nlinarith [Real.pi_gt_three]
  · exact hdef k hKk
end StandardMapEntropy

end OAI
