import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleAcceptance
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawDecidableEq
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

namespace OAI

/-! # The companion phase walk driven by disjoint bounded Boolean words -/

namespace ContingencyTables.CompanionBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev State (A : Instance I J) := ChainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))

def proposalBits (A : Instance I J) : ℕ := Nat.clog 2 (Fintype.card (Labels A)^2)

lemma proposal_codes (A : Instance I J) (S : State A) :
    Fintype.card {T : State A // ExchangeAdjacent S.val T.val} ≤ 2^proposalBits A := by
  rw [Fintype.card_subtype]
  have hh := chain_neighbors_card pairs PairedLabels.fresh PairedLabels.cover S
  simp only [PairedLabels.length] at hh
  exact hh.trans (Nat.le_pow_clog (by decide) _)

/-- Each valid exchange neighbor has one code. Every unused code holds
the current state; the full transition has another independent lazy bit. -/
def proposal (A : Instance I J) (S : State A) (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  subsetBitDraw (fun T : State A => ExchangeAdjacent S.val T.val)
    (proposalBits A) (proposal_codes A S) bits

lemma proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact subsetBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (State A)))
    (fun T : State A => ExchangeAdjacent S.val T.val) (proposalBits A) (proposal_codes A S) T

def stepBits (A : Instance I J) (C K j k : ℕ) (xi : ℚ) : ℕ :=
  1+(proposalBits A+((medianEstimatorBits A C K j xi xi+
    medianEstimatorBits A C K j xi xi)+k))

def stepWordEquiv (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :
    (Fin (stepBits A C K j k xi) → Bool) ≃
      ((Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
        ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool)))) :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((splitWordEquiv _ _).trans (Equiv.prodCongr (splitWordEquiv _ _) (Equiv.refl _))))))

/-- The realized step evaluates the current and proposed weights from
separate words, then uses a third independent word for its rational coin. -/
def step (A : Instance I J) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (stepBits A C K j k xi) → Bool) : State A :=
  let b := stepWordEquiv A C K j k xi bits
  if b.1 0 then S else
    match proposal A S b.2.1 with
    | none => S
    | some T =>
        if rationalThresholdAccept k
          (CompanionOracleAcceptance.acceptance A C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
        then T else S

/-- A nontrivial move uses exactly its proposal code and the fresh
acceptance experiment. Failed codes and the independent holding bit
contribute only to the diagonal. -/
theorem step_eq_iff (A : Instance I J) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : State A) (hST : S ≠ T) (bits : Fin (stepBits A C K j k xi) → Bool) :
    step A C K j k hK hW xi v w S bits=T ↔
      (stepWordEquiv A C K j k xi bits).1 0=false ∧
      proposal A S (stepWordEquiv A C K j k xi bits).2.1=some T ∧
      rationalThresholdAccept k
        (CompanionOracleAcceptance.acceptance A C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2 := by
  dsimp only [step]
  generalize stepWordEquiv A C K j k xi bits = b
  cases b.1 0 with
  | true => simp [hST]
  | false =>
    cases proposal A S b.2.1 with
    | none => simp [hST]
    | some U =>
      by_cases hUT : U=T
      · subst U
        simp [hST]
      · by_cases ha : rationalThresholdAccept k
          (CompanionOracleAcceptance.acceptance A C K j hK hW xi v w S.val U.val b.2.2.1) b.2.2.2
        · simp [hUT,ha]
        · simp [hST,hUT,ha]

def transitionLaw (A : Instance I J) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    RationalLaw (State A) :=
  mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A C K j k hK hW xi v w S)

def walk (A : Instance I J) (C K j k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (n*stepBits A C K j k xi) → Bool) : State A :=
  wordWalk (step A C K j k hK hW xi v w) S n
    (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

/-- The actual flattened word gives independent repeated transitions;
its law follows from the finite-word walk construction. -/
theorem walk_law (A : Instance I J) (C K j k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (walk A C K j k n hK hW xi v w S)=
        walkLaw (transitionLaw A C K j k hK hW xi v w) S n := by
  unfold walk
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  exact wordWalkLaw_eq _ _ _

private lemma dyadic_size_le_twice (n : ℕ) (hn : 0 < n) : 2^Nat.clog 2 n ≤ 2*n := by
  by_cases h1 : n=1
  · subst n
    norm_num
  have hgt : 1 < n := by omega
  have hm : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hgt
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hgt
  have he : Nat.clog 2 n=(Nat.clog 2 n).pred+1 := (Nat.succ_pred_eq_of_pos hm).symm
  calc
    _ = 2*2^(Nat.clog 2 n).pred := by
      conv_lhs => rw [he,pow_succ]
      ring
    _ ≤ 2*n := Nat.mul_le_mul_left 2 hp.le

def slowdown (A : Instance I J) : ℝ :=
  (Fintype.card (Labels A):ℝ)^2/(2:ℝ)^proposalBits A

/-- The unused proposal codes slow the source chain by at most two;
they do not change its stationary law. -/
theorem slowdown_bounds (A : Instance I J) (hp : 0 < Fintype.card (Labels A)) :
    (1/2:ℝ) ≤ slowdown A ∧ slowdown A ≤ 1 := by
  have hn : 0 < Fintype.card (Labels A)^2 := pow_pos hp _
  have hl := dyadic_size_le_twice (Fintype.card (Labels A)^2) hn
  have hu := Nat.le_pow_clog (by decide : 1<2) (Fintype.card (Labels A)^2)
  have hlR : (2:ℝ)^proposalBits A ≤ 2*(Fintype.card (Labels A):ℝ)^2 := by exact_mod_cast hl
  have huR : (Fintype.card (Labels A):ℝ)^2 ≤ (2:ℝ)^proposalBits A := by exact_mod_cast hu
  unfold slowdown
  constructor
  · rw [le_div_iff₀ (by positivity : (0:ℝ)<2^proposalBits A)]
    linarith
  · exact (div_le_one (by positivity)).mpr huR

end

end ContingencyTables.CompanionBooleanPhase

end OAI
