import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRangeRealization
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSamplerCoupling

namespace OAI

/-! # Word refinements for the prime calls used in both branches -/

noncomputable section
namespace LowSpaceSubsetSum.WordRealization

def prime (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w) :
    Realization w (n^3) (primeCoupling hell n) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  exact map (rejection w ell hw (n^3) (primeEligible ell)) (primeEligibleEquiv hell)

def factor (w n ell : ℕ) (hw : ell ≤ w) :
    Realization w (n^3) (factorCoupling n ell) := by
  unfold factorCoupling
  split
  next h => exact enlarge (map (pure ()) (factorOneEquiv h)) (Nat.zero_le _)
  next h => exact map (prime w n ell (by omega) hw) (factorPrimeEquiv (by omega))

def triplePrime (w n a b c : ℕ) (ha : a ≤ w) (hb : b ≤ w) (hc : c ≤ w) :
    Realization w (3*n^3) (triplePrimeCoupling n a b c) := by
  have h := map (prod (prod (factor w n a ha) (factor w n b hb))
    (factor w n c hc)) (tripleFactorEquiv a b c)
  simpa only [triplePrimeCoupling, show (n^3+n^3)+n^3 = 3*n^3 by omega] using h

def compression {n : ℕ} (D : CompressionData n) (hn : 168000000 ≤ n)
    (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hq : compressionPrimeExponent n ≤ w) :
    Realization w (n*n^3+n^3) (D.sampler hn) :=
  bind (permutation w n n hp) (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)
    (fun _ => prime w n (compressionPrimeExponent n)
      (by unfold compressionPrimeExponent; omega) hq)

end LowSpaceSubsetSum.WordRealization

end

end OAI
