import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPermutationExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimeInitialization

namespace OAI

/-! # Actual word-driven compression sampler

The permutation generator retains its range candidate buffers. The prime
width is computed by one multiplication and one division before its
modulus and bounded rejection routine. Exhaustion remains `none`.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

private def compressionCore {n : ℕ} (D : CompressionData n) (hn : 168000000 ≤ n)
    (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hq : compressionPrimeExponent n ≤ w) :
    Execution (WordSeedRealization.compression D hn w hp hq) :=
  let ell := 249*n/1000
  bind (permutation w n n hp) (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)
    (fun _ => WordSeedRealization.prime w n ell (by omega) hq)
    (fun _ => primeInitialized w n ell (by omega) hq)

def compression {n : ℕ} (D : CompressionData n) (hn : 168000000 ≤ n)
    (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hq : compressionPrimeExponent n ≤ w) :
    Execution (WordSeedRealization.compression D hn w hp hq) where
  run stream cursor :=
    let out := (compressionCore D hn w hp hq).run stream cursor
    ⟨out.accepted,out.cursor,out.work+6,max 8 (out.cells+8),out.retained+1⟩
  value stream cursor := (compressionCore D hn w hp hq).value stream cursor

def compressionWork (n : ℕ) : ℕ :=
  n*(13*n^3+5*n+64)+
    (n^3*(12*2^((compressionPrimeExponent n+1)/2)+
      12*(compressionPrimeExponent n+1)+11)+3*compressionPrimeExponent n+17)+9

theorem compression_bounded {n : ℕ} (D : CompressionData n) (hn : 168000000 ≤ n)
    (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hq : compressionPrimeExponent n ≤ w) :
    (compression D hn w hp hq).Bounded (compressionWork n)
      ((n+3)*(2*n^3+256)) ((n+2)*(n^3+64)) := by
  have hh := bind_bounded (permutation w n n hp)
    (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)
    (fun _ => WordSeedRealization.prime w n (compressionPrimeExponent n)
      (by unfold compressionPrimeExponent; omega) hq)
    (fun _ => primeInitialized w n (compressionPrimeExponent n)
      (by unfold compressionPrimeExponent; omega) hq)
    _ _ _ _ _ _ (permutation_bounded w n n hp)
    (fun _ => primeInitialized_bounded w n (compressionPrimeExponent n)
      (by unfold compressionPrimeExponent; omega) hq)
  intro stream cursor
  have h := hh stream cursor
  dsimp only [compression,compressionCore]
  change _+6 ≤ compressionWork n ∧ max 8 (_+8) ≤ (n+3)*(2*n^3+256) ∧
    _+1 ≤ (n+2)*(n^3+64)
  refine ⟨?_,?_,?_⟩
  · have hwork := Nat.add_le_add_right h.1 6
    apply hwork.trans
    unfold compressionWork
    omega
  · apply max_le
    · nlinarith
    · have hc := Nat.add_le_add_right h.2.1 8
      apply hc.trans
      have hA : (n+1)*(2*n^3+256)+8 ≤ (n+3)*(2*n^3+256) := by nlinarith
      have hB : ((n+1)*(n^3+64)+(2*n^3+124)+8)+8 ≤
          (n+3)*(2*n^3+256) := by nlinarith
      omega
  · have hr := Nat.add_le_add_right h.2.2 1
    exact hr.trans (by nlinarith)

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
