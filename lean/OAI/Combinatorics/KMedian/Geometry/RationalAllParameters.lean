import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationParameters
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters

namespace OAI


                                             
section
namespace MetricKMedian.Preparation

structure RationalAllParameters (η τ : ℝ) where
  round : FixedBatch.RationalParameters τ
  even : Even round.Δ
  M : ℚ
  δ : ℚ
  γ : ℚ
  T₁ : ℚ
  hM : 0<M
  hδ : 0<δ
  hδ1 : (δ:ℝ)≤1/4
  hγ : 0<γ
  hγ1 : γ≤1
  hT : 0<T₁
  hθ : 1/((M:ℝ)*(δ:ℝ))≤1/8
  hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ))≤1/4
  failure : failureFactor (γ:ℝ) (round.g:ℝ)<1
  error : max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ)))
              ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
          (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (round.g:ℝ)) /
          (1-failureFactor (γ:ℝ) (round.g:ℝ)) ≤ 1+η

 theorem exists_rational_all_parameters {η τ : ℝ} (hη : 0<η) (hτ : 0<τ) :
    Nonempty (RationalAllParameters η τ) := by
  obtain ⟨δ,M,T₁,γ,hδ,hδ1,hM,hT,hγ,hγ1,hθ,hα,g₀,hg₀,hg⟩ := exists_preparation_parameters hη
  obtain ⟨D₀,hD⟩ := all_fine_grids hg₀
  obtain ⟨q,hq,heven⟩ := FixedBatch.exists_rational_parameters hτ D₀
  have heq : (q.g:ℝ)=1/(q.Δ:ℝ) := (eq_div_iff (by exact_mod_cast q.Δpos.ne')).mpr q.unit
  have hsmall : (q.g:ℝ) ≤ g₀ := heq ▸ (hD q.Δ hq).2.2
  have he := hg (q.g:ℝ) q.gpos hsmall
  exact ⟨{
    round := q
    even := heven
    M := M
    δ := δ
    γ := γ
    T₁ := T₁
    hM := by exact_mod_cast hM
    hδ := by exact_mod_cast hδ
    hδ1 := hδ1
    hγ := by exact_mod_cast hγ
    hγ1 := by exact_mod_cast hγ1
    hT := by exact_mod_cast hT
    hθ := hθ
    hα := hα
    failure := by linarith only [he.1]
    error := he.2 }⟩

end MetricKMedian.Preparation
end

end OAI
