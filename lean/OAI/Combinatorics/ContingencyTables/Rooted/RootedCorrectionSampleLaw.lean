import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSampleProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSamples

namespace OAI

/-! # Exact law of the executed correction sample

The two coordinate enumerations need not agree on a fixed bit string.
Their independent finite-word laws agree, which preserves every real
observable of the computed rational sample.
-/

namespace ContingencyTables.RootedCorrectionSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FairBits
open CommonBasesFPRAS FiniteLawMoments
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

local instance freeCellDecidableEq (A : Instance (Fin m) (Fin n)) :
    DecidableEq (FreeCell A.small A.T) := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  infer_instance

private lemma bind_equiv {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : RationalLaw X) (e : X ≃ Y) (f : Y → RationalLaw Z) :
    bindLaw (equivLaw e p) f=bindLaw p (fun x => f (e x)) := by
  apply RationalLaw.ext
  funext z
  change (∑ y,p.mass (e.symm y)*(f y).mass z)=∑ x,p.mass x*(f (e x)).mass z
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

abbrev Words (A : Instance (Fin m) (Fin n)) (C N h : ℕ) :=
  (Fin (N*oracleStepBits A C) → Bool) × (Fin (RootedBinDrawLaw.wordBits A h) → Bool)

def integerDraw (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ)
    (bits : Words A C N h) : FreeIndex A.small A.T A.b :=
  RootedBinDrawLaw.flatDraw A K (by omega) hW
    (RootedOracleWalkProgram.flatGridWalk A C a z v N bits.1) h bits.2

lemma integerDraw_law (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) :
    mapLaw (uniformLaw (α := Words A C N h)) (integerDraw A C a K hK hW z v N h)=
      RootedOracleDensity.sampledIntegerLaw A (RootedCompletion.rowColumn A.T) C a z K hK hW
        (RootedCatalogGrid.gridEquiv A K v) N h := by
  unfold integerDraw
  rw [←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (N*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (RootedBinDrawLaw.wordBits A h) → Bool))
    (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w bits => RootedBinDrawLaw.flatDraw A K (by omega) hW w h bits)]
  rw [RootedOracleWalkProgram.flatGridWalk_law]
  have hb (w : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :=
    RootedBinDrawLaw.flatDraw_law A K (by omega) hW w h
  simp_rw [hb]
  rw [RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB]
  rw [bind_equiv]
  unfold RootedOracleDensity.sampledIntegerLaw
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB]
  congr 1
  funext w
  simp only [Equiv.apply_symm_apply]

def sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (sigma : ℚ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ)
    (bits : Words A C N h) : ℚ :=
  RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K
    (by omega) sigma (integerDraw A C a K hK hW z v N h bits)

/-- Equality for arbitrary observables is exact equality in distribution
of the executed rational sample and the analysed correction sample. -/
theorem sample_average (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z) (sigma : ℚ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) (g : ℚ → ℝ) :
    uniformAverage (fun bits : Words A C N h => g (sample A C a K hK hW z sigma v N h bits))=
      uniformAverage (fun bits : Fin (oracleIntegerBits A C N h) → Bool =>
        g (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C a z K
          hK hW sigma (RootedCatalogGrid.gridEquiv A K v) N h bits)) := by
  let obs := fun f : FreeIndex A.small A.T A.b =>
    g (RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K
      (by omega) sigma f)
  have hleft := word_expectation (integerDraw A C a K hK hW z v N h) obs
  have hright := word_expectation
    (RootedOracleDensity.oracleIntegerDraw A (RootedCompletion.rowColumn A.T) C a z K hK hW
      (RootedCatalogGrid.gridEquiv A K v) N h) obs
  rw [integerDraw_law A C a K hC haH hK hW hKB z hz v N h] at hleft
  rw [RootedOracleDensity.oracleIntegerDraw_law] at hright
  exact hleft.trans hright.symm

theorem program_sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (sigma : ℚ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N h : ℕ) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma) (bits : Words A C N h) :
    MatchingFPRAS.TreeFraction.val (RootedCorrectionSampleProgram.output
      (RootedCorrectionSampleProgram.data A C a K z v h degree depth
        (List.ofFn bits.1) (List.ofFn bits.2)))=
      sample A C a K hK hW z sigma v N h bits :=
  RootedCorrectionSampleProgram.output_data A C a K hC haH (by omega) hW hB z v h
    degree depth sigma hdegree hdepth N bits.1 bits.2

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
