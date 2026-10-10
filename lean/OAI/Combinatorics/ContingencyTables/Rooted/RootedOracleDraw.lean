import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleFiniteStep
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleDraw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def stationaryIntegerLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleStationaryLaw A R C a z hK) (exactBinLaw A K (by omega) hW)

/-- The stationary bin draw followed by the actual uniform integer
interval draw is precisely the corrected mass used in the exact h identity. -/
theorem stationaryIntegerLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (f : FreeIndex A.small A.T A.b) :
    ((stationaryIntegerLaw A R C a z K hK hW).mass f:ℝ)=correctedMass A R C a z K (by omega) f := by
  change ((∑ v,(oracleStationaryLaw A R C a z hK).mass v*
    (exactBinLaw A K (by omega) hW v).mass f:ℚ):ℝ)=_
  simp only [Rat.cast_sum,Rat.cast_mul,exactBinLaw_mass,oracleStationaryLaw_cast,
    oracleChain_pi,apply_ite,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_zero]
  calc
    _ = ∑ v : Grid (I := Fin (dimension A)) K,
        if integerBin A K (by omega) f=v then
          gridWeight A R C a z v/binSum A R C a z K/(integerFiber A K (by omega) v).card else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [binSum,div_eq_mul_inv,one_mul,mul_zero]
    _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,correctedMass]

def sampledIntegerLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleBitWalkLaw A R C a z v n) (fun w => approximateBinLaw A K (by omega) hW w h)

/-- Both errors are accounted for once: mixing of the actual bin walk,
then bounded quotient sampling inside its selected bin. -/
theorem sampledIntegerLaw_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (sampledIntegerLaw A R C a z K hK hW v (oracleTime A C K Q theta) h)
      (stationaryIntegerLaw A R C a z K hK hW):ℝ) ≤
      theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)) := by
  have hb := variation_bind_uniform (oracleBitWalkLaw A R C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A R C a z hK) (fun w => approximateBinLaw A K (by omega) hW w h)
    (exactBinLaw A K (by omega) hW) ((A.d:ℚ)/(2:ℚ)^(4*(h+A.d)))
    (fun w => approximateBinLaw_variation A K (by omega) hW w h)
  have hbR := (Rat.cast_le (K := ℝ)).mpr hb
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] at hbR
  exact hbR.trans (add_le_add
    (oracleBitWalkLaw_variation A R C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v) le_rfl)


def flatOracleWalk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ)
    (bits : Fin (n*oracleStepBits A C) → Bool) : Grid (I := Fin (dimension A)) K :=
  wordWalk (oracleBitStep A R C a z) v n (oracleWalkWordEquiv n (oracleStepBits A C) bits)

lemma flatOracleWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool)) (flatOracleWalk A R C a z v n)=
      oracleBitWalkLaw A R C a z v n := by
  unfold flatOracleWalk
  rw [←map_equiv (oracleWalkWordEquiv n (oracleStepBits A C)),uniform_equiv]
  rfl

def oracleIntegerDraw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ)
    (bits : Fin (oracleIntegerBits A C n h) → Bool) : FreeIndex A.small A.T A.b :=
  let draws := splitWordEquiv (n*oracleStepBits A C) (binWordBits A h) bits
  flatBinDraw A K (by omega) hW (flatOracleWalk A R C a z v n draws.1) h draws.2

/-- One fixed Boolean word drives the bin walk and then the integer draw.
The bin-dependent interval length never changes the reserved word length. -/
theorem oracleIntegerDraw_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    mapLaw (uniformLaw (α := Fin (oracleIntegerBits A C n h) → Bool))
      (oracleIntegerDraw A R C a z K hK hW v n h)=sampledIntegerLaw A R C a z K hK hW v n h := by
  unfold oracleIntegerDraw oracleIntegerBits
  dsimp only
  rw [←map_equiv (splitWordEquiv (n*oracleStepBits A C) (binWordBits A h))
    (uniformLaw (α := Fin (n*oracleStepBits A C+binWordBits A h) → Bool))
    (fun draws => flatBinDraw A K (by omega) hW (flatOracleWalk A R C a z v n draws.1) h draws.2),
    uniform_equiv,←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (binWordBits A h) → Bool))
    (flatOracleWalk A R C a z v n) (fun w bits => flatBinDraw A K (by omega) hW w h bits),
    flatOracleWalk_law]
  unfold sampledIntegerLaw
  congr 1
  funext w
  exact flatBinDraw_law A K (by omega) hW w h

end
end ContingencyTables.RootedOracleDensity

end OAI
