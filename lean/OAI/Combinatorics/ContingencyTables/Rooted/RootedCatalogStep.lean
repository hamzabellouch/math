import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogGrid
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleFiniteStep

namespace OAI

/-! # The actual oracle transition in computed catalog order

Axis proposals are uniform over a bounded dyadic code space. Changing
the coordinate order preserves their frequencies, even though it need
not preserve the value obtained from an individual proposal word.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (oracleStepBits rationalHeight)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma freeCount_eq (A : Instance (Fin m) (Fin n)) :
    freeCount A=CompanionOracleDensity.dimension A := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (RootedForestCatalog.freeEquiv A)

lemma freeCount_le (A : Instance (Fin m) (Fin n)) : freeCount A≤A.d := by
  rw [freeCount_eq]
  exact ForestScaledPenalty.free_card_le A

def exponent (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) : ℕ :=
  RootedOracleDensity.gridExponent A (rowColumn A.T) C a z (gridEquiv A K v)

def finiteStepLaw (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    RationalLaw (Grid (I := Fin (freeCount A)) K) :=
  finiteAcceptLaw v (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (exponent A C a z w-exponent A C a z v) (rationalHeight A C))

theorem finiteStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    finiteStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z (gridEquiv A K v)) := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hw
  have hvw : v≠w := Ne.symm hw
  have he : gridEquiv A K v≠gridEquiv A K w :=
    fun h => hvw ((gridEquiv A K).injective h)
  change (finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun b => acceptDyadic (exponent A C a z b-exponent A C a z v)
      (rationalHeight A C))).mass w=
    (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z
      (gridEquiv A K v)).mass (gridEquiv A K w)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hvw,
    RootedOracleDensity.finiteOracleStepLaw,
    finiteAcceptLaw_off_diagonal (gridEquiv A K v) (gridEquiv A K w) _ _ he,
    axisCodeStep_count (dense_proposal_code_bound A.d (freeCount A) (freeCount_le A)),
    axisCodeStep_count (dense_proposal_code_bound A.d (CompanionOracleDensity.dimension A)
      (ForestScaledPenalty.free_card_le A)),neighbor_iff]
  rfl

def bitStep (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K)
    (bits : Fin (oracleStepBits A C) → Bool) : Grid (I := Fin (freeCount A)) K :=
  let draw := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C) bits
  match axisCodeStep v draw.1 with
  | none => v
  | some w => if draw.2.val < 2^(rationalHeight A C-(exponent A C a z w-exponent A C a z v))
      then w else v

def bitStepLaw (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    RationalLaw (Grid (I := Fin (freeCount A)) K) :=
  mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (bitStep A C a z v)

lemma bitStepLaw_eq_finite (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=finiteStepLaw A C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (exponent A C a z w-exponent A C a z v) (rationalHeight A C))
  have hf : bitStep A C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [bitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold bitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

/-- The actual catalog-order finite-word experiment has the exact
transition law of the oracle mixing theorem. -/
theorem bitStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a≤rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK (gridEquiv A K v)) := by
  rw [bitStepLaw_eq_finite,finiteStepLaw_eq,
    RootedOracleDensity.finiteOracleStepLaw_eq A (rowColumn A.T) C a hC haH z hz hK hKB]

end
end ContingencyTables.RootedCatalogGrid

end OAI
