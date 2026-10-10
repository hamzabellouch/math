import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedStructuralExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedPrimes

namespace OAI

/-! # Executing the dependent representation sampling history

Every continuation uses the cached accepted layout. At the prime stages it
runs the counted mixer preparation on that layout's stored accepted seed.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {n : ℕ}

private theorem clog_le (k w : ℕ) (h : k ≤ w) : Nat.clog 2 k ≤ w :=
  (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans h

def guessHistory (I : Instance n) (w : ℕ) (hw : n+1 ≤ w) :
    Execution (WordSeedRealization.guessHistory (canonicalRepresentationData I).zeroSetup w hw) := by
  have hg : CanonicalGuesses.width n ≤ n+1 := by
    unfold CanonicalGuesses.width CanonicalGuesses.upper CanonicalGuesses.lower mixerSize
    omega
  exact bind (layout _ w (clog_le _ _ (by omega)) (by omega))
    (fun _ => RepresentationSetup.Guesses n) (fun _ => (canonicalRepresentationData I).zeroSetup.guessesCoupling)
    (fun _ => WordSeedRealization.guesses _ w (clog_le _ _ (hg.trans hw)))
    (fun _ => guesses _ w (clog_le _ _ (hg.trans hw)))

def partitionHistory (I : Instance n) (w : ℕ) (hw : n+1 ≤ w) :
    Execution (WordSeedRealization.partitionHistory (canonicalRepresentationData I).zeroSetup w hw) :=
  bind (guessHistory I w hw) (fun h => (canonicalRepresentationData I).zeroSetup.Partitions h.1)
    (fun h => (canonicalRepresentationData I).zeroSetup.partitionsCoupling h.1)
    (fun h => WordSeedRealization.partitions _ h.1 w (by omega))
    (fun h => partitions _ h.1 w (by omega))

def layoutOfPartition (I : Instance n)
    (a : Accepted (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling) :
    WordLayoutPreparation.Layout I :=
  firstAccepted (fun _ => RepresentationSetup.Guesses n)
    (fun _ => (canonicalRepresentationData I).zeroSetup.guessesCoupling)
    (firstAccepted (fun h => (canonicalRepresentationData I).zeroSetup.Partitions h.1)
      (fun h => (canonicalRepresentationData I).zeroSetup.partitionsCoupling h.1) a)

def primeHistory (I : Instance n) (w : ℕ) (hw : n+1 ≤ w) :
    Execution (WordSeedRealization.primeHistory (canonicalRepresentationData I).zeroSetup w hw) :=
  bindSeed (partitionHistory I w hw)
    (fun h => (canonicalRepresentationData I).zeroSetup.PrimeSpace h.1.1)
    (fun h => (canonicalRepresentationData I).zeroSetup.nestedCoupling h.1.1)
    (fun h => WordSeedRealization.nested _ h.1.1 w (by omega))
    (fun a => nestedPrepared I (layoutOfPartition I a) w (by omega))

def residues (R : RepresentationSetup n) (hn : 1 ≤ n)
    {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z) (w : ℕ) (hw : 3*n ≤ w) :
    Execution (WordSeedRealization.residues R hn p w hw) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  have h (i : Fin 3) : Nat.clog 2 (prefixModulus p.val i) ≤ w :=
    (Nat.clog_le_of_le_pow (RepresentationScalarBounds.prefix_bound R hn z p i)).trans hw
  exact prepareThen (fun _ => (((),6),8)) (fun _ =>
    prod (fin w n _ (h 0)) (prod (fin w n _ (h 1)) (fin w n _ (h 2))))

def trialHistory (I : Instance n) (hn : 1 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Execution (WordSeedRealization.trialHistory (canonicalRepresentationData I).zeroSetup hn w hw) :=
  bind (primeHistory I w (by omega))
    (fun h => (canonicalRepresentationData I).zeroSetup.Residues h.2)
    (fun h => (canonicalRepresentationData I).zeroSetup.residuesCoupling h.2)
    (fun h => WordSeedRealization.residues _ hn h.2 w (by omega))
    (fun h => residues _ hn h.2 w (by omega))

def layoutOfTrial (I : Instance n)
    (a : Accepted (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling) :
    WordLayoutPreparation.Layout I :=
  layoutOfPartition I
    (firstAccepted (fun h => (canonicalRepresentationData I).zeroSetup.PrimeSpace h.1.1)
      (fun h => (canonicalRepresentationData I).zeroSetup.nestedCoupling h.1.1)
      (firstAccepted (fun h => (canonicalRepresentationData I).zeroSetup.Residues h.2)
        (fun h => (canonicalRepresentationData I).zeroSetup.residuesCoupling h.2) a))

def extraHistory (I : Instance n) (hn : 100 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Execution (WordSeedRealization.extraHistory (canonicalRepresentationData I).zeroSetup hn w hw) :=
  bindSeed (trialHistory I (by omega) w hw)
    (fun h => (canonicalRepresentationData I).zeroSetup.ExtraPrimeSpace h.1.1.1.1)
    (fun h => (canonicalRepresentationData I).zeroSetup.extraPrimeCoupling h.1.1.1.1 hn)
    (fun h => WordSeedRealization.extraPrime _ h.1.1.1.1 hn w (by omega))
    (fun a => extraPrepared I (layoutOfTrial I a) hn w (by omega))

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
