import OAI.Analysis.FreeEntropy.GaussianEntropyIntegrability

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem integral_coordinate_ibp (i : ι) (f f' g g' : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀x r,HasDerivAt (fun t : ℝ => f (x+t • EuclideanSpace.single i 1)) (f' (x+r • EuclideanSpace.single i 1)) r)
    (hg : ∀x r,HasDerivAt (fun t : ℝ => g (x+t • EuclideanSpace.single i 1)) (g' (x+r • EuclideanSpace.single i 1)) r)
    (hfg' : Integrable (fun x => f x*g' x)) (hf'g : Integrable (fun x => f' x*g x))
    (hfg : Integrable (fun x => f x*g x)) :
    (∫x,f x*g' x) = -(∫x,f' x*g x) := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hf'g hfg' hfg
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hf x 0
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hg x 0
end FiniteEntropySeparation

end

end OAI
