import OAI.NumberTheory.CubicMoment.Angular.AngularShortTuplePartition
import OAI.NumberTheory.CubicMoment.Estimates.PartitionMoment

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def primaryAngularUnsplitTuple (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryAngularTupleCore ℓ A a b q η t V Y n

end CubicFirstMoment

end

end OAI
