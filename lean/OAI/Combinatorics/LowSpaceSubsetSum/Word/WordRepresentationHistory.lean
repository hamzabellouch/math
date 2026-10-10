import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRepresentationDraws
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScalarBounds

namespace OAI

/-! # Exact word programs for the complete dependent representation history -/

noncomputable section
namespace LowSpaceSubsetSum.WordRealization

private theorem clog_le (k w : ℕ) (h : k ≤ w) : Nat.clog 2 k ≤ w :=
  (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans h

def partitions {n : ℕ} (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (w : ℕ) (hw : n ≤ w) : Realization w (3*(n*n^3)) (R.partitionsCoupling z) :=
  pi w (n*n^3) 3 _ _ (fun i => by
    have hs : RepresentationSetup.blockCount i * (2*RepresentationSetup.blockHalf n i) ≤ n := by
      rw [← CanonicalPartition.size_eq R z i]
      simpa only [Fintype.card_fin] using Finset.card_le_univ (R.orderedMixers z i)
    exact enlarge (partition R z i w (clog_le _ _ (hs.trans hw)))
      (Nat.mul_le_mul_right _ hs))

def nested {n : ℕ} (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (w : ℕ) (hw : n ≤ w) : Realization w (3*n^3) (R.nestedCoupling z) :=
  triplePrime w n _ _ _ ((R.factorExponents_le_n z 0).trans hw)
    ((R.factorExponents_le_n z 1).trans hw) ((R.factorExponents_le_n z 2).trans hw)

def residues {n : ℕ} (R : RepresentationSetup n) (hn : 1 ≤ n)
    {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z) (w : ℕ) (hw : 3*n ≤ w) :
    Realization w (n^3+(n^3+n^3)) (R.residuesCoupling p) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  have h (i : Fin 3) : Nat.clog 2 (prefixModulus p.val i) ≤ w :=
    (Nat.clog_le_of_le_pow (RepresentationScalarBounds.prefix_bound R hn z p i)).trans hw
  exact prod (fin w n _ (h 0)) (prod (fin w n _ (h 1)) (fin w n _ (h 2)))

def extraPrime {n : ℕ} (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (hn : 100 ≤ n) (w : ℕ) (hw : n ≤ w) :
    Realization w (n^3) (R.extraPrimeCoupling z hn) :=
  prime w n _ (R.extraPrimeParameter_range z hn).1
    ((R.extraPrimeParameter_range z hn).2.trans hw)

def guessHistory {n : ℕ} (R : RepresentationSetup n) (w : ℕ) (hw : n+1 ≤ w) :
    Realization w ((n*n^3+n)+3*n^3) R.guessHistoryCoupling := by
  have hg : CanonicalGuesses.width n ≤ n+1 := by
    unfold CanonicalGuesses.width CanonicalGuesses.upper CanonicalGuesses.lower mixerSize
    omega
  exact bind (layout R w (clog_le _ _ (by omega)) (by omega))
    (fun _ => RepresentationSetup.Guesses n) (fun _ => R.guessesCoupling)
    (fun _ => guesses R w (clog_le _ _ (hg.trans hw)))

def partitionHistory {n : ℕ} (R : RepresentationSetup n) (w : ℕ) (hw : n+1 ≤ w) :
    Realization w (((n*n^3+n)+3*n^3)+3*(n*n^3)) R.partitionHistoryCoupling :=
  bind (guessHistory R w hw) (fun h => R.Partitions h.1)
    (fun h => R.partitionsCoupling h.1) (fun h => partitions R h.1 w (by omega))

def primeHistory {n : ℕ} (R : RepresentationSetup n) (w : ℕ) (hw : n+1 ≤ w) :
    Realization w ((((n*n^3+n)+3*n^3)+3*(n*n^3))+3*n^3) R.primeHistoryCoupling :=
  bind (partitionHistory R w hw) (fun h => R.PrimeSpace h.1.1)
    (fun h => R.nestedCoupling h.1.1) (fun h => nested R h.1.1 w (by omega))

def trialHistory {n : ℕ} (R : RepresentationSetup n) (hn : 1 ≤ n)
    (w : ℕ) (hw : 3*n+1 ≤ w) :
    Realization w (((((n*n^3+n)+3*n^3)+3*(n*n^3))+3*n^3)+(n^3+(n^3+n^3)))
      R.trialHistoryCoupling :=
  bind (primeHistory R w (by omega)) (fun h => R.Residues h.2)
    (fun h => R.residuesCoupling h.2) (fun h => residues R hn h.2 w (by omega))

def extraHistory {n : ℕ} (R : RepresentationSetup n) (hn : 100 ≤ n)
    (w : ℕ) (hw : 3*n+1 ≤ w) :
    Realization w ((((((n*n^3+n)+3*n^3)+3*(n*n^3))+3*n^3)+(n^3+(n^3+n^3)))+n^3)
      (R.extraHistoryCoupling hn) := by
  unfold RepresentationSetup.extraHistoryCoupling
  exact bind (S := R.trialHistoryCoupling) (trialHistory R (by omega) w hw) (fun h => R.ExtraPrimeSpace h.1.1.1.1)
    (fun h => R.extraPrimeCoupling h.1.1.1.1 hn)
    (fun h => extraPrime R h.1.1.1.1 hn w (by omega))

def historyReads (n : ℕ) : ℕ :=
  ((((((n*n^3+n)+3*n^3)+3*(n*n^3))+3*n^3)+(n^3+(n^3+n^3)))+n^3)+
    4*(11*2^(2*RepresentationSetup.blockHalf n 0)*((2*RepresentationSetup.blockHalf n 0)*n^3))

def separatorDraws {n : ℕ} (R : RepresentationSetup n)
    (h : R.PrimeHistory) (hn : 2200 ≤ n) (w : ℕ)
    (hw : Nat.clog 2 (2*RepresentationSetup.blockHalf n 0) ≤ w) :
    Realization w (4*(11*2^(2*RepresentationSetup.blockHalf n 0)*
      ((2*RepresentationSetup.blockHalf n 0)*n^3))) (R.separatorCoupling h hn) :=
  families (RepresentationSetup.separatorParameters h.1.1.2 hn) w n hw

def bucketHistory {n : ℕ} (R : RepresentationSetup n) (hn : 10000 ≤ n)
    (w : ℕ) (hw : 3*n+1 ≤ w) :=
  bind (S := R.extraHistoryCoupling (by omega)) (extraHistory R (by omega) w hw)
    (fun h => R.SeparatorDraws h.1.1 (by omega))
    (fun h => R.separatorCoupling h.1.1 (by omega))
    (fun h => separatorDraws R h.1.1 (by omega) w (clog_le _ _ (by
        have hg : 2*RepresentationSetup.blockHalf n 0 ≤ n := by
          unfold RepresentationSetup.blockHalf
          simp only [Matrix.cons_val_zero]
          omega
        omega)))

end LowSpaceSubsetSum.WordRealization

end

end OAI
