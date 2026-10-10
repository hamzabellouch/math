import Mathlib
import OAI.Analysis.Commutator.Pairings

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

lemma repr_lt_apply (σ : Pairing J) (j : J) : repr σ j < σ (repr σ j) := by
  rcases lt_or_gt_of_ne (σ.apply_ne j).symm with hj | hj
  · simpa only [repr, min_eq_left (le_of_lt hj)] using hj
  · simpa only [repr, min_eq_right (le_of_lt hj), apply_apply] using hj

end Kadison.Pairing
end

end OAI
