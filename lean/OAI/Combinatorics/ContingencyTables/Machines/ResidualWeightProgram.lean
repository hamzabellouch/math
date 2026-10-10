import OAI.Combinatorics.ContingencyTables.Transport.IntegerResidualCorrection
import OAI.Combinatorics.ContingencyTables.Machines.VectorRetryProgram

namespace OAI

/-! # Binary computation of the rare branch's integer weights -/

namespace ContingencyTables.ResidualWeightPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

abbrev Input := (ℕ×ℕ)×(ℕ×ℕ)

/-- Common denominator, inverse branch probability, number of tables,
and the ordinary draw's numerator. -/
def count (z : Input) : ℕ := z.1.1*z.1.2-z.2.1*(z.1.2-1)*z.2.2

def countRealizer : Realizer count := by
  let denominator : Realizer (fun z : Input => z.1.1) := composition first first
  let branch : Realizer (fun z : Input => z.1.2) := composition first second
  let cardinality : Realizer (fun z : Input => z.2.1) := composition second first
  let numerator : Realizer (fun z : Input => z.2.2) := composition second second
  let left := composition (pair denominator branch) multiply
  let right := composition (pair (composition (pair cardinality
    (composition branch predecessor)) multiply) numerator) multiply
  exact composition (pair left right) subtract

lemma polynomial_count : PolynomialTime countRealizer := by
  unfold countRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_predecessor)) polynomial_multiply)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply))
    polynomial_subtract

lemma count_actual {A : Type*} [Fintype A] {Q : ℕ} (p : IntegerLaw A Q)
    (T : ℕ) (hT : 0<T) (a : A) :
    count ((Q,T),(Fintype.card A,p.count a))=IntegerResidualCorrection.count p T a := by
  have ht : (T:ℤ)-1=((T-1:ℕ):ℤ) := by omega
  have he : ResidualMixture.residualNumerator Q T (fun x => (p.count x:ℤ)) a=
      ((Q*T:ℕ):ℤ)-((Fintype.card A*(T-1)*p.count a:ℕ):ℤ) := by
    unfold ResidualMixture.residualNumerator
    rw [ht]
    push_cast
    rfl
  rw [IntegerResidualCorrection.count,he,Int.toNat_sub]
  rfl

end ContingencyTables.ResidualWeightPrograms

end OAI
