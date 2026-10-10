import OAI.Combinatorics.ContingencyTables.Rooted.RootedRatioSampleProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport

namespace OAI

/-! # The executed ratio sample has the exact analysed law -/

namespace ContingencyTables.RootedRatioSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FiniteLawMoments
open CommonBasesFPRAS FiniteObservableTransport
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

private lemma expectation_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : RationalLaw X) (f : Y → ℝ) :
    expectation (equivLaw e p) f=expectation p (fun x => f (e x)) := by
  unfold expectation equivLaw
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

def sample (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) : ℚ :=
  RootedOracleDensity.rationalRatioObservable A (RootedCompletion.rowColumn A.T) C a z
    (RootedCatalogGrid.gridEquiv A K (RootedOracleWalkProgram.flatGridWalk A C a z v N bits))

theorem sameLaw (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    SameLaw (sample A C a z v N)
      (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) N) := by
  intro g
  let obs := fun w : Grid (I := Fin (dimension A)) K =>
    g (RootedOracleDensity.rationalRatioObservable A (RootedCompletion.rowColumn A.T) C a z w)
  have hl := word_expectation (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w => obs (RootedCatalogGrid.gridEquiv A K w))
  rw [RootedOracleWalkProgram.flatGridWalk_law,
    RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB,expectation_equiv] at hl
  simp only [Equiv.apply_symm_apply] at hl
  have hr := word_expectation
    (wordWalk (RootedOracleDensity.oracleBitStep A (RootedCompletion.rowColumn A.T) C a z)
      (RootedCatalogGrid.gridEquiv A K v) N) obs
  change uniformAverage (fun bits => g (RootedOracleDensity.ratioSample A
    (RootedCompletion.rowColumn A.T) C a z (RootedCatalogGrid.gridEquiv A K v) N bits))=
      expectation (RootedOracleDensity.oracleBitWalkLaw A (RootedCompletion.rowColumn A.T)
        C a z (RootedCatalogGrid.gridEquiv A K v) N) obs at hr
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB] at hr
  exact hl.trans hr.symm

lemma program_sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) :
    MatchingFPRAS.TreeFraction.val (RootedRatioSampleProgram.output
      (RootedOracleWalkProgram.data A C a K z v,List.ofFn bits))=sample A C a z v N bits :=
  RootedRatioSampleProgram.output_data A C a K hC z hz hKB v N bits

end
end ContingencyTables.RootedRatioSampleLaw

end OAI
