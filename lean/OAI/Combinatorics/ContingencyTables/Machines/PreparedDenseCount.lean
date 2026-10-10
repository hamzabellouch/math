import OAI.Combinatorics.ContingencyTables.Dense.DenseCountProgram
import OAI.Combinatorics.ContingencyTables.Machines.BoundedPowerProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseTransitionCounts

namespace OAI

/-! # Polynomial transition entries with a shared acceptance allowance -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev PreparedCountInput := List Bool×CountInput

def preparedGap (z : PreparedCountInput) : ℕ :=
  flatExponent (replaceFlat z.2)-flatExponent z.2.1

def preparedGapRealizer : Realizer preparedGap :=
  composition (pair
    (composition (composition second replaceFlatRealizer) flatExponentRealizer)
    (composition (composition second first) flatExponentRealizer)) subtract

lemma polynomial_preparedGap : PolynomialTime preparedGapRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_replaceFlat)
      polynomial_flatExponent)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_flatExponent)) polynomial_subtract

def preparedOffCount (z : PreparedCountInput) : ℕ :=
  if hasProposal (countProposalInput z.2) then
    BoundedPowerPrograms.power (z.1,preparedGap z) else 0

def preparedOffCountRealizer : Realizer preparedOffCount := by
  let pin : Realizer (fun z : PreparedCountInput => (z.1,preparedGap z)) :=
    pair first preparedGapRealizer
  let powered := composition pin BoundedPowerPrograms.powerRealizer
  exact choose (composition (composition second countProposalInputRealizer) hasProposalRealizer)
    powered (constant 0)

/-- The allowance is supplied once. Enumerating a row or the whole matrix
then uses only polynomial-time operations on binary entries. -/
theorem polynomial_preparedOffCount : PolynomialTime preparedOffCountRealizer := by
  unfold preparedOffCountRealizer
  exact polynomial_choose
    (polynomial_composition (polynomial_composition polynomial_second polynomial_countProposalInput)
      polynomial_hasProposal)
    (polynomial_composition (polynomial_pair polynomial_first polynomial_preparedGap)
      BoundedPowerPrograms.polynomial_power) (polynomial_constant 0)

lemma preparedOffCount_eq (xs : List Bool) (z : CountInput) (h : xs.length=8*z.1.2^5) :
    preparedOffCount (xs,z)=offCountCode z := by
  unfold preparedOffCount offCountCode
  simp only [BoundedPowerPrograms.power_eq,BinaryPowerPrograms.power_eq,preparedGap,
    countPowerInput,h]

lemma offCountCode_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    offCountCode ((((marginCode R,marginCode P),gridNatCode a),d),gridNatCode b)=
      FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
  rw [offCountCode_eq]
  by_cases hba : b=a
  · subst b
    have hn : ¬Neighbor a a := fun h => neighbor_ne a a h rfl
    simp [FiniteAcceptCounts.offCount,hn]
  · simp only [FiniteAcceptCounts.offCount,ite_eq_right hba]
    rw [axisCodeStep_count (dense_proposal_code_bound d (m*n) hq)]
    split_ifs <;> simp

end ContingencyTables.DensePrograms

end OAI
