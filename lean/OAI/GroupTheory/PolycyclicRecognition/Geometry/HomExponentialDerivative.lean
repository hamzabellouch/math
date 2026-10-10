import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieConjugationDifferential

namespace OAI

/-! # Reading a homomorphism differential from an exponential line -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]

omit [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem mfderiv_hom_eq_of_exponential_line
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (φ : G →* G) (hφ : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ 1)
    (x y : GroupLieAlgebra (𝓘(ℝ,E)) G)
    (hline : ∀ t : ℝ, φ (Exp (t • x)) = Exp (t • y)) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ 1 x = y := by
  have hφ' : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ (Exp ((0 : ℝ) • x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ 1) := by
    rw [zero_smul,hExp.map_zero]
    exact hφ.hasMFDerivAt
  have hd := hφ'.comp 0 (hExp.hasMFDerivAt_zero x)
  have he : (fun t : ℝ => φ (Exp (t • x))) = (fun t : ℝ => Exp (t • y)) := funext hline
  change HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => φ (Exp (t • x))) 0 _ at hd
  rw [he] at hd
  have hD := hd.mfderiv.symm.trans (hExp.hasMFDerivAt_zero y).mfderiv
  have hV := congrArg (fun d : ℝ →L[ℝ] E => d 1) hD
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ 1) ((1 : ℝ) • x) = (1 : ℝ) • y at hV
  simpa only [one_smul] using hV

end PolycyclicRecognition

end

end OAI
