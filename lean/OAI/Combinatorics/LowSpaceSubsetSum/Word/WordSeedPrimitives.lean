import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedConstructors
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordPrimeRealization

namespace OAI

/-! # Successful sampler seeds for the concrete range and prime samplers -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedRealization

def range (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w) :
    Realization w (n^3) (rangeCoupling hD n) := by
  let : Nonempty (Fin D) := ⟨⟨0,by omega⟩⟩
  let : Nonempty {x : Fin (2^Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0,by omega⟩⟩
  exact map (rejection w (Nat.clog 2 D) hw (n^3) (rangeEligible D)) (rangeEligibleEquiv D)

def fin (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) :
    Realization w (n^3) (finCoupling n D) := by
  unfold finCoupling
  split
  next h => exact range w n D h hw
  next => exact enlarge (pure (⟨0,Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D)) (Nat.zero_le _)

def permutation (w n : ℕ) : (k : ℕ) → Nat.clog 2 k ≤ w →
    Realization w (k*n^3) (permutationCoupling n k)
  | 0, _ => by
    simpa only [Nat.zero_mul,permutationCoupling] using (pure (w := w) (Equiv.refl (Fin 0)))
  | k+1, hw => by
    have hk : Nat.clog 2 k ≤ w :=
      (Nat.clog_mono_right 2 (by omega : k ≤ k+1)).trans hw
    have h := map (prod (fin w n (k+1) hw) (permutation w n k hk))
      Equiv.Perm.decomposeFin.symm
    simpa only [permutationCoupling,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

def finiteChoice (w n : ℕ) (A : Type) [Fintype A] [Nonempty A]
    (hw : Nat.clog 2 (Fintype.card A) ≤ w) :
    Realization w (n^3) (finiteChoiceCoupling n A) :=
  map (fin w n (Fintype.card A) hw) (Fintype.equivFin A).symm

def finitePermutation (w n : ℕ) (A : Type) [Fintype A] [DecidableEq A]
    (hw : Nat.clog 2 (Fintype.card A) ≤ w) :
    Realization w (Fintype.card A*n^3) (finitePermutationCoupling n A) :=
  map (permutation w n (Fintype.card A) hw) (Equiv.permCongr (Fintype.equivFin A).symm)

def prime (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w) :
    Realization w (n^3) (primeCoupling hell n) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2^ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  exact map (rejection w ell hw (n^3) (primeEligible ell)) (primeEligibleEquiv hell)

def factor (w n ell : ℕ) (hw : ell ≤ w) :
    Realization w (n^3) (factorCoupling n ell) := by
  unfold factorCoupling
  split
  next h => exact enlarge (map (pure ()) (factorOneEquiv h)) (Nat.zero_le _)
  next => exact map (prime w n ell (by omega) hw) (factorPrimeEquiv (by omega))

def triplePrime (w n a b c : ℕ) (ha : a ≤ w) (hb : b ≤ w) (hc : c ≤ w) :
    Realization w (3*n^3) (triplePrimeCoupling n a b c) := by
  have h := map (prod (prod (factor w n a ha) (factor w n b hb))
    (factor w n c hc)) (tripleFactorEquiv a b c)
  simpa only [triplePrimeCoupling,show (n^3+n^3)+n^3 = 3*n^3 by omega] using h

def compression {n : ℕ} (D : CompressionData n) (hn : 168000000 ≤ n)
    (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hq : compressionPrimeExponent n ≤ w) :
    Realization w (n*n^3+n^3) (D.sampler hn) :=
  bind (permutation w n n hp) (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)
    (fun _ => prime w n (compressionPrimeExponent n)
      (by unfold compressionPrimeExponent; omega) hq)

end LowSpaceSubsetSum.WordSeedRealization

end

end OAI
