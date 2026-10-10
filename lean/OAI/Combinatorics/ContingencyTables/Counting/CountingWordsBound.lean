import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleWordBounds
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingWords
import OAI.Combinatorics.ContingencyTables.Counting.CompanionScaleSizes

namespace OAI

/-! # A polynomial bound for the complete adaptive counting word

The bound includes every reserved restart, oracle and observation word,
including the words unused on unsuccessful paths.
-/

namespace ContingencyTables.CountingWordsBound
open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory
open CountingOracleWordBounds Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def initialPolynomial : Polynomial ℕ := X*(X+1)*(X*(3*X+1)+1+X)
def stepPolynomial : Polynomial ℕ := 1+(X^2+((medianPolynomial+medianPolynomial)+X))
def stagePolynomial : Polynomial ℕ := X*((X+1)*stepPolynomial)
def phasePolynomial : Polynomial ℕ :=
  initialPolynomial+X*stagePolynomial+(X*stepPolynomial+(X+1)*(medianPolynomial+medianPolynomial))
def wordPolynomial : Polynomial ℕ := X*(X*phasePolynomial)

lemma bitCount_bound (A : Instance I J) (s : Settings A) (M : ℕ)
    (hd : A.d ≤ M) (hW : A.W ≤ M) (hK : s.K ≤ M) (hH : s.H ≤ M)
    (hk : s.k ≤ M) (hn : s.n ≤ M) (hN : s.N ≤ M) (hh : s.h ≤ M)
    (hheight : rationalHeight A s.C ≤ M)
    (hcapacity : CountingTerminalSchedule.capacityBits A ≤ M)
    (hlabels : Fintype.card (Labels A) ≤ M)
    (htau : CompanionTargetMixing.restartTime A s.H s.L ≤ M)
    (hxi : 0 < s.xi) (hinverse : 1/s.xi ≤ (M:ℚ))
    (hrepeats : CommonBasesFPRAS.repetitionCount s.xi ≤ 64*(M+1)) :
    RootedCountingWords.bitCount A s ≤ wordPolynomial.eval M := by
  have hmedian (j : ℕ) (hj : j ≤ s.H) :
      medianEstimatorBits A s.C s.K j s.xi s.xi ≤ medianPolynomial.eval M :=
    median_bound A s.C s.K j M s.xi hd hK hheight (hj.trans hH) hcapacity hxi hinverse hrepeats
  have hstep (j : ℕ) (hj : j ≤ s.H) :
      CompanionBooleanPhase.stepBits A s.C s.K j s.k s.xi ≤ stepPolynomial.eval M := by
    have hm := hmedian j hj
    have hp : CompanionBooleanPhase.proposalBits A ≤ M^2 :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)).trans
        (Nat.pow_le_pow_left hlabels 2)
    simp only [stepPolynomial,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one]
    unfold CompanionBooleanPhase.stepBits
    omega
  have hstage (i : ℕ) (hi : i+1 ≤ s.H) :
      RootedRestartWords.stageWidth A s.C s.K s.H s.L s.k s.n s.xi i ≤ stagePolynomial.eval M := by
    simp only [RootedRestartWords.stageWidth,CompanionReturnWords.returnBits,
      stagePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.mul_le_mul htau (Nat.mul_le_mul (Nat.add_le_add_right hn 1) (hstep (i+1) hi))
  have hinitial : CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A s.h) ≤
      initialPolynomial.eval M := by
    apply (CompanionScaleSizes.initialBits_polynomial_bound A s.h).trans
    simp only [initialPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.mul_le_mul (Nat.mul_le_mul hd (Nat.add_le_add_right hW 1))
      (Nat.add_le_add (Nat.add_le_add_right
        (Nat.mul_le_mul hd (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hW) 1)) 1) hh)
  have hwidth (j : ℕ) (hj : j < s.H) : width A s j ≤ phasePolynomial.eval M := by
    have hsum : (∑ i : Fin j,RootedRestartWords.stageWidth A s.C s.K s.H s.L s.k s.n s.xi i.val) ≤
        M*stagePolynomial.eval M := by
      calc
        _ ≤ ∑ _i : Fin j,stagePolynomial.eval M :=
          Finset.sum_le_sum (fun i _ => hstage i.val (by omega))
        _ = j*stagePolynomial.eval M := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hobs : CompanionPhaseWords.phaseBits A s.C s.K j (s.N+1) s.xi ≤
        (M+1)*(medianPolynomial.eval M+medianPolynomial.eval M) := by
      unfold CompanionPhaseWords.phaseBits CompanionPhaseWords.observationBits
      exact Nat.mul_le_mul (Nat.add_le_add_right hN 1)
        (Nat.add_le_add (hmedian j (by omega)) (hmedian (j+1) (by omega)))
    simp only [width,RootedRestartWords.initialStageBits,phasePolynomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.add_le_add (Nat.add_le_add hinitial hsum)
      (Nat.add_le_add (Nat.mul_le_mul hN (hstep j (by omega))) hobs)
  have htotal : totalWidth A s ≤ M*phasePolynomial.eval M := by
    calc
      _ ≤ ∑ _j : Fin s.H,phasePolynomial.eval M := Finset.sum_le_sum (fun j _ => hwidth j.val j.isLt)
      _ = s.H*phasePolynomial.eval M := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hH
  simp only [RootedCountingWords.bitCount,wordPolynomial,Polynomial.eval_mul,Polynomial.eval_X]
  exact Nat.mul_le_mul hH htotal

end
end ContingencyTables.CountingWordsBound

end OAI
