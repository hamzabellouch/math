import OAI.RepresentationTheory.FoulkesHowe.FirstLabels
import OAI.RepresentationTheory.FoulkesHowe.FlattenedForm
import OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial
import OAI.RepresentationTheory.FoulkesHowe.EncodingHomogeneous
import OAI.RepresentationTheory.FoulkesHowe.BlockWeight

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- The scalar polynomial at the k-th stage of the first transfer sequence. -/
def firstPolynomial {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V) (k : ℕ) :
    MvPolynomial (FirstBlock m × κ) ℂ :=
  multilinearPolynomial (flattenedForm T) e (firstLabel r m k)

/-- Direct block degrees of every intermediate polynomial, by counting its labels. -/
theorem firstPolynomial_blockHomogeneous {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (k : ℕ) (u : FirstBlock m) :
    PolynomialWeights.IsBlockHomogeneous u (firstPolynomial T e k)
      (Finset.univ.filter (fun p => firstLabel r m k p = u)).card := by
  classical
  let : DecidableEq (Fin (r+1) × Fin (r+m)) := Classical.decEq _
  unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
  simpa only [firstPolynomial, multilinearPolynomial] using
    (EncodingDegree.blockHomogeneous_expansion
      (fun z => flattenedForm T (fun p => e (z p))) (firstLabel r m k) u)

end Problem346

end

end OAI
