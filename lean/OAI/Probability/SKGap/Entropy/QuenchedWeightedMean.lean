import Mathlib
import OAI.Probability.SKGap.Entropy.NormalizedWeightedMean

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Primary Static

def StableSquareMeanProperty {n : ℕ} (j c r₀ ρ C₀ A : ℝ) (J : Interaction n) : Prop :=
  ∀h:Fin n→ℝ,
    (∀y,vectorNorm (SKGap.tapField j J h y)≤r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v)→
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
      vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
        C₀*ρ+A/Real.sqrt (n:ℝ)*
          (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2))

theorem gaussian_stable_square_mean {j c r₀ : ℝ} (hj : 0<j) (hj1 : j<1)
    (hc : 0<c) (hr₀ : 0<r₀) :
    ∀ρ:ℝ,0<ρ→(physicalNormBound j+4*j)*ρ<r₀→
    ∃A:ℝ,0≤A ∧
      Tendsto (fun n=>(Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬StableSquareMeanProperty j c r₀ ρ
          ((1+(physicalNormBound j+3*j)/c)*(physicalNormBound j+4*j)) A
          (removeDiagonal (goeMatrix (j/n) g))}) atTop (𝓝 0) := by
  intro ρ hρ hbuffer
  obtain ⟨m,ε,hε,hm,he⟩:=choose_selection_depth hρ
  have hbudget : 1≤residualCoefficientBudget j 2 (2*m) 0 :=
    (by norm_num : (1:ℝ)≤2).trans (residualCoefficientBudget_ge j (by norm_num) (2*m) 0)
  obtain ⟨B,W,C,hB,hW,hC,hprob⟩:=gaussian_fixed_norm_recipe_probability hj hj1 hbudget
    (2*m+1) (2*(2*m))
  obtain ⟨A,hA,hAall⟩:=uniform_stable_square_mean m hj.le (physicalNormBound_pos j).le
    hc hr₀ hρ hε hbuffer hm he hB hW hC.le
  refine ⟨A,hA,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measure_mono
  intro g hg
  by_contra hnot
  have hev : RecipeMatrixEvent j (physicalNormBound j)
      (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m))
      (removeDiagonal (goeMatrix (j/n) g)) := by simpa using hnot
  apply hg
  intro h hst
  apply hAall (by omega) _ h _ _ hev hst
  · change (removeDiagonal (goeMatrix (j/n) g))ᵀ=removeDiagonal (goeMatrix (j/n) g)
    simp [removeDiagonal,Matrix.transpose_sub,goeMatrix_transpose]
  · intro i
    simp [removeDiagonal]

end SKGapCutoff.Recipe

end
end

end OAI
