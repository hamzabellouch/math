import Mathlib
import OAI.Probability.SKGap.Stability.StableRootInverse
import OAI.Probability.SKGap.Entropy.QuenchedWeightedMean
import OAI.Probability.SKGap.Localization.DisorderRecipeEvent

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary Primary Static

theorem disorder_stable_square_mean {β c r₀ : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hc : 0<c) (hr₀ : 0<r₀) :
    ∀ρ:ℝ,0<ρ→(physicalNormBound (β^2)+4*β^2)*ρ<r₀→
    ∃A:ℝ,0≤A ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬StableSquareMeanProperty (β^2) c r₀ ρ
          ((1+(physicalNormBound (β^2)+3*β^2)/c)*(physicalNormBound (β^2)+4*β^2)) A
          (coupling g)}) atTop (𝓝 0) := by
  intro ρ hρ hbuffer
  obtain ⟨m,ε,hε,hm,he⟩:=choose_selection_depth hρ
  have hbudget : 1≤residualCoefficientBudget (β^2) 2 (2*m) 0 :=
    (by norm_num : (1:ℝ)≤2).trans (residualCoefficientBudget_ge (β^2) (by norm_num) (2*m) 0)
  obtain ⟨B,W,C,hB,hW,hC,hprob⟩:=disorder_fixed_norm_recipe_probability hβ hβ1 hbudget
    (2*m+1) (2*(2*m))
  obtain ⟨A,hA,hAall⟩:=uniform_stable_square_mean m (sq_nonneg β)
    (physicalNormBound_pos (β^2)).le hc hr₀ hρ hε hbuffer hm he hB hW hC.le
  refine ⟨A,hA,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measure_mono
  intro g hg
  by_contra hnot
  have hev : RecipeMatrixEvent (β^2) (physicalNormBound (β^2))
      (residualCoefficientBudget (β^2) 2 (2*m) 0) B W C (2*m+1) (2*(2*m))
      (coupling g) := by simpa using hnot
  apply hg
  intro h hst
  apply hAall (by omega) _ h _ _ hev hst
  · ext i k
    exact coupling_symm g k i
  · exact coupling_diag g

lemma stableSquareMeanProperty_rootBad {n : ℕ} {j A₀ ε c r₀ ρ C₀ C : ℝ}
    (hA₀ : 1≤A₀) (J : Interaction n)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C J) (h : Fin n→ℝ)
    (hbad : ¬rootBad j A₀ ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
      vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
        C₀*ρ+C/Real.sqrt (n:ℝ)*
          (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2)) := by
  apply H h
  intro y hy
  apply stable_hessian_coercive hbad hy
  · intro i
    exact ⟨(spinVariance_pos y i).le,(spinVariance_le_one y i).trans hA₀⟩
  · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    positivity

end SKGapCutoff.Recipe

end
end

end OAI
