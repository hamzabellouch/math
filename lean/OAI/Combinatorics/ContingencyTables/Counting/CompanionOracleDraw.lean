import OAI.Combinatorics.ContingencyTables.Counting.CompanionBinIntervals
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleFiniteStep
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalkApproximation

namespace OAI

/-! # Actual bounded Boolean draws for the companion correction experiment -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binSize_le_range (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (i : Fin (dimension A)) :
    binSize A K v i ≤ freeRange A (index A i) := by
  have hN : 0 < freeRange A (index A i) := Nat.succ_pos _
  have he := FairBits.fiber_card hK hN (naturalBin_lt A v (index A i))
  have hc : (FairBits.fiber K (freeRange A (index A i)) (naturalBin A v (index A i))).card ≤
      freeRange A (index A i) := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  rw [he] at hc
  exact hc

abbrev BinWords (A : Instance I J) (h : ℕ) :=
  (i : Fin (dimension A)) → Fin (offsetBitLength (freeRange A (index A i)) h A.d) → Bool

def binWordBits (A : Instance I J) (h : ℕ) : ℕ :=
  ∑ i : Fin (dimension A),offsetBitLength (freeRange A (index A i)) h A.d

def binWordEquiv (A : Instance I J) (h : ℕ) :
    (Fin (binWordBits A h) → Bool) ≃ BinWords A h :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.piCurry (fun _ _ => Bool))

lemma binBits_le (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (i : Fin (dimension A)) :
    offsetBitLength (binSize A K v i) h A.d ≤
      offsetBitLength (freeRange A (index A i)) h A.d := by
  unfold offsetBitLength
  exact Nat.add_le_add_right (Nat.clog_mono_right 2
    (Nat.add_le_add_right (binSize_le_range A K hK v i) 1)) _

def binWordDraw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (bits : BinWords A h) :
    FreeIndex A.small A.T A.b :=
  binOffsetValue A K hK v (fun i => scaledBitInteger (binSize A K v i)
    (offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)
    (prefixWord (binBits_le A K hK v h i) (bits i)))

/-- The bin-dependent interval length only chooses a prefix of the
fixed per-coordinate word. This preserves the analyzed quotient law. -/
theorem binWordDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := BinWords A h)) (binWordDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold binWordDraw approximateBinLaw
  rw [←mapLaw_comp,←pi_uniformLaw]
  rw [pi_mapLaw (fun i : Fin (dimension A) =>
    uniformLaw (α := Fin (offsetBitLength (freeRange A (index A i)) h A.d) → Bool))
    (fun i bits => scaledBitInteger (binSize A K v i)
      (offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)
      (prefixWord (binBits_le A K hK v h i) bits))]
  congr 1
  congr 1
  funext i
  rw [padded_draw_law]
  exact scaledBitIntegerLaw_eq _ _ _

def flatBinDraw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (bits : Fin (binWordBits A h) → Bool) :
    FreeIndex A.small A.T A.b := binWordDraw A K hK hW v h (binWordEquiv A h bits)

lemma flatBinDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (binWordBits A h) → Bool)) (flatBinDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold flatBinDraw
  rw [←map_equiv (binWordEquiv A h),uniform_equiv,binWordDraw_law]

def stationaryIntegerLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleStationaryLaw A C a z hK) (exactBinLaw A K (by omega) hW)

/-- The stationary bin draw followed by the actual uniform integer
interval draw is precisely the corrected mass used in the exact h identity. -/
theorem stationaryIntegerLaw_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (f : FreeIndex A.small A.T A.b) :
    ((stationaryIntegerLaw A C a z K hK hW).mass f:ℝ)=correctedMass A C a z K (by omega) f := by
  change ((∑ v,(oracleStationaryLaw A C a z hK).mass v*
    (exactBinLaw A K (by omega) hW v).mass f:ℚ):ℝ)=_
  simp only [Rat.cast_sum,Rat.cast_mul,exactBinLaw_mass,oracleStationaryLaw_cast,
    oracleChain_pi,apply_ite,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_zero]
  calc
    _ = ∑ v : Grid (I := Fin (dimension A)) K,
        if integerBin A K (by omega) f=v then
          gridWeight A C a z v/binSum A C a z K/(integerFiber A K (by omega) v).card else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [binSum,div_eq_mul_inv,one_mul,mul_zero]
    _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,correctedMass]

def sampledIntegerLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleBitWalkLaw A C a z v n) (fun w => approximateBinLaw A K (by omega) hW w h)

/-- Both errors are accounted for once: mixing of the actual bin walk,
then bounded quotient sampling inside its selected bin. -/
theorem sampledIntegerLaw_variation (A : Instance I J) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (sampledIntegerLaw A C a z K hK hW v (oracleTime A C K Q theta) h)
      (stationaryIntegerLaw A C a z K hK hW):ℝ) ≤
      theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)) := by
  have hb := variation_bind_uniform (oracleBitWalkLaw A C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A C a z hK) (fun w => approximateBinLaw A K (by omega) hW w h)
    (exactBinLaw A K (by omega) hW) ((A.d:ℚ)/(2:ℚ)^(4*(h+A.d)))
    (fun w => approximateBinLaw_variation A K (by omega) hW w h)
  have hbR := (Rat.cast_le (K := ℝ)).mpr hb
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] at hbR
  exact hbR.trans (add_le_add
    (oracleBitWalkLaw_variation A C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v) le_rfl)


private lemma map_product_bind {X Y Z T : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype T]
    [DecidableEq Z] [DecidableEq T] (p : RationalLaw X) (q : RationalLaw Y)
    (draw : X → Z) (finish : Z → Y → T) :
    mapLaw (productLaw p q) (fun xy => finish (draw xy.1) xy.2)=
      bindLaw (mapLaw p draw) (fun z => mapLaw q (finish z)) := by
  apply RationalLaw.ext
  funext t
  simp only [mapLaw,productLaw,bindLaw,Fintype.sum_prod_type]
  symm
  calc
    _ = ∑ x,p.mass x*(∑ y,if finish (draw x) y=t then q.mass y else 0) := by
      simp_rw [Finset.sum_mul,ite_mul,zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp

def oracleWalkWordEquiv (n k : ℕ) : (Fin (n*k) → Bool) ≃ (Fin n → Fin k → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def flatOracleWalk (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ)
    (bits : Fin (n*oracleStepBits A C) → Bool) : Grid (I := Fin (dimension A)) K :=
  wordWalk (oracleBitStep A C a z) v n (oracleWalkWordEquiv n (oracleStepBits A C) bits)

lemma flatOracleWalk_law (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool)) (flatOracleWalk A C a z v n)=
      oracleBitWalkLaw A C a z v n := by
  unfold flatOracleWalk
  rw [←map_equiv (oracleWalkWordEquiv n (oracleStepBits A C)),uniform_equiv]
  rfl

def oracleIntegerBits (A : Instance I J) (C n h : ℕ) : ℕ :=
  n*oracleStepBits A C+binWordBits A h

def oracleIntegerDraw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ)
    (bits : Fin (oracleIntegerBits A C n h) → Bool) : FreeIndex A.small A.T A.b :=
  let draws := splitWordEquiv (n*oracleStepBits A C) (binWordBits A h) bits
  flatBinDraw A K (by omega) hW (flatOracleWalk A C a z v n draws.1) h draws.2

/-- One fixed Boolean word drives the bin walk and then the integer draw.
The bin-dependent interval length never changes the reserved word length. -/
theorem oracleIntegerDraw_law (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    mapLaw (uniformLaw (α := Fin (oracleIntegerBits A C n h) → Bool))
      (oracleIntegerDraw A C a z K hK hW v n h)=sampledIntegerLaw A C a z K hK hW v n h := by
  unfold oracleIntegerDraw oracleIntegerBits
  dsimp only
  rw [←map_equiv (splitWordEquiv (n*oracleStepBits A C) (binWordBits A h))
    (uniformLaw (α := Fin (n*oracleStepBits A C+binWordBits A h) → Bool))
    (fun draws => flatBinDraw A K (by omega) hW (flatOracleWalk A C a z v n draws.1) h draws.2),
    uniform_equiv,←uniform_product]
  rw [map_product_bind
    (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (binWordBits A h) → Bool))
    (flatOracleWalk A C a z v n) (fun w bits => flatBinDraw A K (by omega) hW w h bits),
    flatOracleWalk_law]
  unfold sampledIntegerLaw
  congr 1
  funext w
  exact flatBinDraw_law A K (by omega) hW w h

end

end ContingencyTables.CompanionOracleDensity

end OAI
