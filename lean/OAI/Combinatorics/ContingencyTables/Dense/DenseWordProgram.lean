import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisProgram

namespace OAI

/-! # Splitting the actual dense transition word in polynomial time -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

lemma clog_two_eq_size_pred (n : ℕ) : Nat.clog 2 n=(n-1).size := by
  cases n with
  | zero => simp
  | succ n =>
    apply Nat.le_antisymm
    · apply (Nat.clog_le_iff_le_pow (by decide)).mpr
      have h := Nat.lt_size_self n
      simpa only [Nat.add_sub_cancel] using Nat.succ_le_of_lt h
    · apply Nat.size_le.mpr
      have h := Nat.le_pow_clog (by decide : 1<2) (n+1)
      simpa only [Nat.add_sub_cancel] using Nat.lt_of_succ_le h

def ceilLogTwoRealizer : Realizer (Nat.clog 2) :=
  (composition predecessor bitSize).congr (fun n => (clog_two_eq_size_pred n).symm)

theorem polynomial_ceilLogTwo : PolynomialTime ceilLogTwoRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_predecessor polynomial_bitSize)

def proposalWidth (z : FlatExponentData×List Bool) : ℕ := Nat.clog 2 (8*z.1.2)

def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : FlatExponentData×List Bool => z.1.2) := composition first second
  let M := composition (pair (constant 8) D) multiply
  exact composition M ceilLogTwoRealizer

theorem polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatExponentData) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

def flatWordStep (z : FlatExponentData×List Bool) : List ℕ :=
  flatMetropolisStep (z.1,
    (z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))

def flatWordStepRealizer : Realizer flatWordStep :=
  composition (pair first (pair
    (composition (pair second proposalWidthRealizer) takeFast)
    (composition (pair second proposalWidthRealizer) dropFast))) flatMetropolisStepRealizer

theorem polynomial_flatWordStep : PolynomialTime flatWordStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth) polynomial_dropFast)))
    polynomial_flatMetropolisStep

end ContingencyTables.DensePrograms

end OAI
