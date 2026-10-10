import OAI.NumberTheory.TwoPoint.Bounds.ActualWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.AffineWeightedWordComparison

namespace OAI

/-! The concrete signed masked word on a fixed arithmetic progression
of origins, preserving the original residue-model expectation. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

local instance affineWordPrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (i : Fin (Fintype.card ↥(data.P ∪ data.Q))) :
    NeZero (primeResidueModuli (data.P ∪ data.Q) i) :=
  ⟨(primeResidueModuli_prime _ (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩

theorem BravermanDepth22Input.eventually_actual_affine_word_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M R s B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → ((J + M : ℕ) : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      0 < R → ((R + 1 : ℕ) : ℝ) ≤ 4 * L → ((R * J : ℕ) : ℝ) ≤ L ^ 2 →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (P : Fin J → Finset ℕ)
        (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ i, ((padding i).primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (label : Fin R × Fin J → ↥(data.P ∪ data.Q)),
      (∀ i j, (label (i, j)).val = (w j i).val) →
      wordDisplacement h (columnTupleWord w forward padding) = 0 →
      ∀ (eligible : ℕ → ℕ → Prop) (K : ℝ) (a l N : ℕ),
      (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient eligible
        (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L K
        (fun _ => actualPaddingDegreeCut data.Q L) h
        (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z)
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward padding)) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward padding))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcomp⟩ := hBr.eventually_affine_weighted_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcomp, eventually_ge_atTop (4800 : ℝ)] with L hcomp hL
  intro h J M R s B data hB hpool hBL hs hJM hpairs hR hRL hRJ Q hQ P w forward padding
    hprime hdisjoint hdeg label hlabel hclosed eligible K a l N hl hN
  let m := Fintype.card ↥data.Q
  let e : Fin m ≃ data.Q := (Fintype.equivFin ↥data.Q).symm
  let primes := data.P ∪ data.Q
  let modulus := primeResidueModuli primes
  let (i : Fin (Fintype.card primes)) : NeZero (modulus i) :=
    ⟨(primeResidueModuli_prime primes (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩
  let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
  let literal := actualWordLiterals data s e step label
  let F := fun z : ∀ i, ZMod (modulus i) => actualWordBoolean data s Q e step
    (fun i j => (w j i).val) eligible L K
    (residueCircuitInputs modulus (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal) z)
  have hp : ∀ p ∈ primes, p.Prime := fun p hp => data.prime ⟨p, hp⟩
  have hcard : (Fintype.card primes : ℝ) ≤ Real.exp L := by
    have hb := primePool_card_bound primes hp B hB
    have hb' : (primes.card : ℝ) ≤ B := by exact_mod_cast hb
    simpa only [Fintype.card_coe] using hb'.trans hBL
  have hm : (m : ℝ) ≤ Real.exp L := by
    have he : m = data.Q.card := by simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e
    rw [he]
    have hq : (data.Q.card : ℝ) ≤ primes.card := by
      exact_mod_cast card_le_card (subset_union_right : data.Q ⊆ primes)
    exact hq.trans (by simpa only [Fintype.card_coe] using hcard)
  have hpzero : 0 < Fintype.card primes := by
    simpa only [Fintype.card_coe] using card_pos.mpr hpool
  have hmod : ∀ i, (modulus i : ℝ) ≤ Real.exp L := by
    intro i
    exact primeResidueModuli_bound primes (Real.exp L)
      (fun p hp => (show (p : ℝ) ≤ B by exact_mod_cast hB p hp).trans hBL) i
  have hR' : (R : ℝ) ≤ 4 * L := by push_cast at hRL; linarith
  have hsize := prohibitedWordKeepCircuit_size_budget data.pairs h s (J + M)
    (actualWordBadIndex data s R m) L (by linarith) hRL hs hJM hpairs
    (data.pair_primeFactors_card)
  have hc := hcomp (Fintype.card primes) modulus hpzero (by linarith)
    (primeResidueModuli_coprime primes hp) hmod (R + 1) m (R * J) _ ⌊400 * Real.log L⌋₊
    hm (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))) hRL hRJ
    (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal)
    (actualWordQIndex data s R m) (actualWordPIndex data s R m)
    (actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step (fun i j => (w j i).val))
    (prohibitedWordKeepCircuit data.pairs h s (actualWordBadIndex data s R m))
    (fun b => actualWordCoefficient_budget data.Q Q e (fun t => eligible t.tuple) L K step _
      (fun i j => hprime j _ (w j i).property) hL hR' hdeg _ _)
    ((prohibitedWordKeepCircuit_depth data.pairs h s _).trans (by norm_num)) hsize a l N (fun i => hl _ ((Fintype.equivFin primes).symm i).property) hN
  change |uniformAverage (fun x : Fin N => F (fun i => (a + l * x.val : ZMod (modulus i)))) -
    uniformAverage F| ≤ Real.exp (-(L ^ 9)) at hc
  let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient eligible
    (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L K
    (fun _ => actualPaddingDegreeCut data.Q L) h
    (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z)
  have hF (n : ℤ) : F (fun i => (n : ZMod (modulus i))) =
      scalarWalkProduct h weight n (columnTupleWord w forward padding) :=
    actualWordBoolean_integer data s Q hQ e w forward padding hprime hdisjoint label hlabel
      eligible L K (by linarith) n hR hclosed
  have hmodel : (data.residueLaw B hB).average (fun r =>
      scalarWalkProduct h weight (data.residueOrigin r) (columnTupleWord w forward padding)) =
      uniformAverage F := by
    rw [← data.residue_average_canonical hB F]
    apply congrArg (data.residueLaw B hB).average
    funext r
    rw [← hF, data.canonical_origin]
  dsimp only
  rw [hmodel]
  have hsample : (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
      (columnTupleWord w forward padding)) =
      (fun x : Fin N => F (fun i => (a + l * x.val : ZMod (modulus i)))) := by
    funext x
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul] using
      (hF (a + l * x.val)).symm
  rw [hsample]
  exact hc

end TwoPointCorrelations

end OAI
