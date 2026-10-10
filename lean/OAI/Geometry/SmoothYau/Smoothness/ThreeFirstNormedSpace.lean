import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeFirstNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeFirstContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance sphereFirst_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
lemma threeComplexPower_chart_first (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) 0 v =
      (k:ℂ)*(planarLinear a b (p.1:Euclidean 3))^(k-1)*
        planarLinear a b (unitSphereFrame (n:=2) p.1 v.fst)*(p.2:ℂ)^k+
      (planarLinear a b (p.1:Euclidean 3))^k*(k:ℂ)*(p.2:ℂ)^(k-1)*
        unitSphereFrame (n:=1) p.2 v.snd := by
  rw [threeComplexPower_chart]
  erw [directional_mul_complex
    ((productSphere_fstPower_smooth _ _ _).differentiable (by simp))
    ((productSphere_sndPower_smooth _ _ _).differentiable (by simp))]
  erw [productSphere_fstPower_first,productSphere_sndPower_first,
    productSphere_fstPower_zero,productSphere_sndPower_zero]
  simp only [complexIdentityPlanar]
  ring
lemma threePower_chart_first (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threePower a b k ∘ (chartAt ThreeModel p).symm) 0 v =
      ((k:ℂ)*(planarLinear a b (p.1:Euclidean 3))^(k-1)*
        planarLinear a b (unitSphereFrame (n:=2) p.1 v.fst)*(p.2:ℂ)^k+
      (planarLinear a b (p.1:Euclidean 3))^k*(k:ℂ)*(p.2:ℂ)^(k-1)*
        unitSphereFrame (n:=1) p.2 v.snd).re := by
  change fderiv ℝ (fun x => (threeComplexPower a b k ((chartAt ThreeModel p).symm x)).re) 0 v = _
  exact (fderiv_real_part ((threeComplexPower_chart_smooth a b k p).differentiable (by simp) 0) v).trans
    (congrArg Complex.re (threeComplexPower_chart_first a b k p v))
end YauCounterexamples
end

end OAI
