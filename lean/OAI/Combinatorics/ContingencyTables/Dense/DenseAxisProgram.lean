import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisProposal

namespace OAI

/-! # Bounded binary coordinate moves in the dense grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev AxisData := ((ℕ×List ℕ)×ℕ)×Bool

def axisListStep (z : AxisData) : Option (List ℕ) :=
  let K := z.1.1.1
  let xs := z.1.1.2
  let i := z.1.2
  if i<xs.length then
    if z.2 then
      if xs.getD i 0+1<K then some (listExchange (xs,(i,xs.length))) else none
    else
      if 0<xs.getD i 0 then some (listExchange (xs,(xs.length,i))) else none
  else none

def axisListStepRealizer : Realizer axisListStep := by
  let K : Realizer (fun z : AxisData => z.1.1.1) :=
    composition (composition first first) first
  let X : Realizer (fun z : AxisData => z.1.1.2) :=
    composition (composition first first) second
  let I : Realizer (fun z : AxisData => z.1.2) := composition first second
  let L := composition X listLength
  let V := composition (pair X I) (getDFast 0)
  let up := composition (composition (pair X (pair I L)) listExchangeRealizer) TreeTyped.some
  let down := composition (composition (pair X (pair L I)) listExchangeRealizer) TreeTyped.some
  exact (choose (composition (pair I L) less)
    (choose second (choose (composition (pair (composition V successor) K) less)
      up (constant none))
      (choose (composition (pair (constant 0) V) less) down (constant none)))
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,axisListStep])

/-- An invalid or boundary move terminates immediately. Its index is
never used as an iteration count. -/
theorem polynomial_axisListStep : PolynomialTime axisListStepRealizer := by
  have hK : PolynomialTime (composition
      (composition (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hX : PolynomialTime (composition
      (composition (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hI : PolynomialTime (composition
      (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hL := polynomial_composition hX polynomial_listLength
  have hV := polynomial_composition (polynomial_pair hX hI) (polynomial_getDFast 0)
  have hup := polynomial_composition (polynomial_composition
    (polynomial_pair hX (polynomial_pair hI hL)) polynomial_listExchange) polynomial_some
  have hdown := polynomial_composition (polynomial_composition
    (polynomial_pair hX (polynomial_pair hL hI)) polynomial_listExchange) polynomial_some
  unfold axisListStepRealizer
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair hI hL) polynomial_less)
    (polynomial_choose polynomial_second
      (polynomial_choose (polynomial_composition (polynomial_pair
        (polynomial_composition hV polynomial_successor) hK) polynomial_less)
        hup (polynomial_constant none))
      (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_constant 0) hV)
        polynomial_less) hdown (polynomial_constant none))) (polynomial_constant none))

end ContingencyTables.DensePrograms

end OAI
