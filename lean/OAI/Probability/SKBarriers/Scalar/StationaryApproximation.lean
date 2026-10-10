import Mathlib
import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit
import OAI.Probability.SKBarriers.Parisi.QuantileStationarity

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem exists_stationary_quantile_approximation (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ A : Fin (k+1) → ℝ,
      A ∈ admissibleQuantiles k ∧
      (∀ B ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β B) ∧
      extendedQuantileParisi k β A < finiteParisiInf β+ε ∧
      (∀ B ∈ admissibleQuantiles k, 0 ≤ (β^2/2)*∑ j : Fin (k+1),
        ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*(A j-quantileOverlapMean k β A j)) := by
  obtain ⟨p,hp,hlt⟩ := exists_lt_of_csInf_lt (finiteParisiValues_nonempty β)
    (show sInf (finiteParisiValues β) < finiteParisiInf β+ε by
      change finiteParisiInf β < finiteParisiInf β+ε
      linarith)
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  obtain ⟨A,hA,hmin⟩ := exists_finite_quantile_minimizer k β
  exact ⟨k,A,hA,hmin,(hmin Q ⟨hm,hQ⟩).trans_lt hlt,
    fun B hB => finite_quantile_minimizer_stationary β A hA hmin B hB⟩

theorem exists_stationary_quantile_sequence (β : ℝ) :
    ∃ K : ℕ → ℕ, ∃ A : (n : ℕ) → Fin (K n+1) → ℝ,
      (∀ n, A n ∈ admissibleQuantiles (K n)) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) →
        extendedQuantileParisi (K n) β (A n) ≤ extendedQuantileParisi (K n) β B) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) → 0 ≤ (β^2/2)*∑ j : Fin (K n+1),
        ((K n+1:ℕ):ℝ)⁻¹*(B j-A n j)*(A n j-quantileOverlapMean (K n) β (A n) j)) ∧
      Tendsto (fun n => extendedQuantileParisi (K n) β (A n)) atTop (𝓝 (finiteParisiInf β)) := by
  have H (n : ℕ) := exists_stationary_quantile_approximation β
    (show 0 < 1/((n:ℝ)+1) by positivity)
  choose K A ha hm hu hs using H
  refine ⟨K,A,ha,hm,hs,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => finiteParisiInf β+1/((n:ℝ)+1)) atTop (𝓝 (finiteParisiInf β)) from ?_)
    (fun n => finiteParisiInf_le β (A n) (ha n).1 (ha n).2) (fun n => (hu n).le)
  simpa only [add_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (finiteParisiInf β)

end SK.Analytic

end
end

end

end OAI
