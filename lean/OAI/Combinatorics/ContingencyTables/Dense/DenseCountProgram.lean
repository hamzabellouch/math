import OAI.Combinatorics.ContingencyTables.Transport.AxisProposalTest
import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisProgram

namespace OAI

/-! # Executable dense off-diagonal counts without acceptance-word enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped Classical

abbrev CountInput := FlatExponentData×List ℕ

def countProposalInput (z : CountInput) : ProposalTestData :=
  ((4*z.1.2^8,z.1.1.2),z.2)

def countProposalInputRealizer : Realizer countProposalInput := by
  let D : Realizer (fun z : CountInput => z.1.2) := composition first second
  let K := composition (pair (constant 4) (composition D eighthPower)) multiply
  let X : Realizer (fun z : CountInput => z.1.1.2) :=
    composition (composition first first) second
  exact pair (pair K X) second

lemma polynomial_countProposalInput : PolynomialTime countProposalInputRealizer := by
  have hd : PolynomialTime (composition (first (A := FlatExponentData) (B := List ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hK := polynomial_composition (polynomial_pair (polynomial_constant 4)
    (polynomial_composition hd polynomial_eighthPower)) polynomial_multiply
  unfold countProposalInputRealizer
  exact polynomial_pair (polynomial_pair
    hK
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)) polynomial_second

def countPowerInput (z : CountInput) : ℕ×ℕ :=
  (2,8*z.1.2^5-(flatExponent (replaceFlat (z.1,z.2))-flatExponent z.1))

def countPowerInputRealizer : Realizer countPowerInput :=
  pair (constant 2) (composition (pair
    (composition (pair (constant 8) (composition (composition first second) fifthPower)) multiply)
    (composition (pair (composition (composition (pair first second) replaceFlatRealizer)
      flatExponentRealizer) (composition first flatExponentRealizer)) subtract)) subtract)

lemma polynomial_countPowerInput : PolynomialTime countPowerInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 8)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_fifthPower)) polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_pair polynomial_first polynomial_second) polynomial_replaceFlat)
        polynomial_flatExponent)
      (polynomial_composition polynomial_first polynomial_flatExponent)) polynomial_subtract))
    polynomial_subtract)

def offCountCode (z : CountInput) : ℕ :=
  if hasProposal (countProposalInput z) then BinaryPowerPrograms.power (countPowerInput z) else 0

def offCountCodeRealizer : Realizer offCountCode :=
  choose (composition countProposalInputRealizer hasProposalRealizer)
    (composition countPowerInputRealizer BinaryPowerPrograms.powerRealizer) (constant 0)

def countMeasure (z : CountInput) : ℕ := z.1.2^5+weight z

/-- Even a huge acceptance denominator only increases binary integer
length. The exponent and the supplied state encodings bound the work. -/
theorem work_offCountCode : WorkBound offCountCodeRealizer countMeasure := by
  have hb {X : Type} [Codec X] {f : CountInput → X} {F : Realizer f}
      (hF : PolynomialTime F) : WorkBound F countMeasure :=
    work_of_polynomial hF Polynomial.X (fun z => by
      simp only [Polynomial.eval_X,countMeasure]
      omega)
  unfold offCountCodeRealizer
  apply work_choose (hb (polynomial_composition polynomial_countProposalInput polynomial_hasProposal))
    _ (hb (polynomial_constant 0)) Polynomial.X
    (fun z => by simp only [Polynomial.eval_X,countMeasure]; omega)
  apply work_composition (hb polynomial_countPowerInput) BinaryPowerPrograms.work_power
    (8*Polynomial.X+9)
  intro z
  have hw : weight (2:ℕ)≤9 := by decide
  simp only [countPowerInput,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,countMeasure]
  omega

theorem offCountCode_eq {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    offCountCode ((((marginCode R,marginCode P),gridNatCode a),d),gridNatCode b)=
      if Neighbor a b then
        2^(8*d^5-(denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a))
      else 0 := by
  unfold offCountCode countProposalInput countPowerInput replaceFlat
  rw [BinaryPowerPrograms.power_eq,flatExponent_code,flatExponent_code]
  by_cases h : Neighbor a b
  · simp [(hasProposal_code a b).mpr h,h]
  · have hp : hasProposal ((4*d^8,gridNatCode a),gridNatCode b)=false :=
      Bool.eq_false_iff.mpr (fun he => h ((hasProposal_code a b).mp he))
    simp [hp,h]

end ContingencyTables.DensePrograms

end OAI
