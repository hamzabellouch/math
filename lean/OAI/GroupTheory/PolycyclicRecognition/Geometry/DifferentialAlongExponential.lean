import OAI.GroupTheory.PolycyclicRecognition.Geometry.HomExponentialDerivative

namespace OAI

/-! # Recovering a differential from exponential curves -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]

theorem mfderiv_apply_eq_of_exponential_line
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    {f : G → V} (hf : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,V)) f 1)
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G) (y : V)
    (hline : HasDerivAt (fun t : ℝ => f (Exp (t • x))) y 0) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,V)) f 1 x = y := by
  have hf' : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,V)) f (Exp ((0 : ℝ) • x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,V)) f 1) := by
    rw [zero_smul,hExp.map_zero]
    exact hf.hasMFDerivAt
  have hd := hf'.comp 0 (hExp.hasMFDerivAt_zero x)
  have hl := hline.hasFDerivAt.hasMFDerivAt
  have hh := hd.mfderiv.symm.trans hl.mfderiv
  have hv := congrArg (fun A : ℝ →L[ℝ] V => A 1) hh
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,V)) f 1) ((1 : ℝ) • x) = (1 : ℝ) • y at hv
  simpa only [one_smul] using hv

end PolycyclicRecognition

end

end OAI
