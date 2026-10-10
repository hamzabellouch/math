import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimeInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasuredTransport

namespace OAI

/-! # Initialized nested-prime seed execution

Widths below four use the constant unit factor. Every larger factor executes
its modulus construction, actual bounded prime test, and retained candidate
buffer. Tuple assembly has an explicit fixed charge.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

def factorWork (n ell : ℕ) : ℕ :=
  n^3*(12*2^((ell+1)/2)+12*(ell+1)+11)+3*ell+21

def factor (w n ell : ℕ) (hw : ell ≤ w) :
    Execution (WordSeedRealization.factor w n ell hw) :=
  if h : ell < 4 then
    transportSampler (by simp only [factorCoupling,dite_eq_left h])
      (source_factor_small w n ell hw h)
      (enlarge (map (pure (w := w) ()) (factorOneEquiv h)
        (fun a => (((factorOneEquiv h) a,2),2)) (fun _ => rfl)) (Nat.zero_le (n^3)))
  else
    transportSampler (by simp only [factorCoupling,dite_eq_right h])
      (source_factor_large w n ell hw h)
      (map (primeInitialized w n ell (by omega) hw) (factorPrimeEquiv (by omega))
        (fun a => (((factorPrimeEquiv (by omega)) a,2),2)) (fun _ => rfl))

theorem factor_bounded (w n ell : ℕ) (hw : ell ≤ w) :
    (factor w n ell hw).Bounded (factorWork n ell) (2*n^3+124) (n^3+28) := by
  unfold factor
  split
  next h =>
    have hm := map_bounded (pure (w := w) ()) (factorOneEquiv h)
      (fun a => (((factorOneEquiv h) a,2),2)) (fun _ => rfl)
      1 4 4 2 2 (pure_bounded ()) (fun _ => le_rfl) (fun _ => le_rfl)
    apply bounded_mono _ (transportSampler_bounded _ _ _ _ _ _
      (enlarge_bounded _ _ _ _ _ hm))
    · unfold factorWork; omega
    · omega
    · omega
  next h =>
    have hp := primeInitialized_bounded w n ell (by omega) hw
    have hm := map_bounded (primeInitialized w n ell (by omega) hw)
      (factorPrimeEquiv (by omega))
      (fun a => (((factorPrimeEquiv (by omega)) a,2),2)) (fun _ => rfl)
      _ _ _ 2 2 hp (fun _ => le_rfl) (fun _ => le_rfl)
    apply bounded_mono _ (transportSampler_bounded _ _ _ _ _ _ hm)
    · unfold factorWork; omega
    · omega
    · omega

def triplePrime (w n a b c : ℕ) (ha : a ≤ w) (hb : b ≤ w) (hc : c ≤ w) :
    Execution (WordSeedRealization.triplePrime w n a b c ha hb hc) :=
  reprogram
    (map (prod (prod (factor w n a ha) (factor w n b hb)) (factor w n c hc))
      (tripleFactorEquiv a b c)
      (fun p => (((tripleFactorEquiv a b c) p,8),8)) (fun _ => rfl)) (by
        conv_lhs => rw [WordSeedRealization.triplePrime]
        exact mpr_program (w := w) (α := ↥(tripleRange a b c))
          (by omega : 3*n^3 = (n^3+n^3)+n^3) _)

theorem triplePrime_bounded (w n a b c : ℕ) (ha : a ≤ w) (hb : b ≤ w) (hc : c ≤ w) :
    (triplePrime w n a b c ha hb hc).Bounded
      (factorWork n a+factorWork n b+factorWork n c+20)
      (4*n^3+256) (3*n^3+136) := by
  have hp := prod_bounded (factor w n a ha) (factor w n b hb) _ _ _ _ _ _
    (factor_bounded w n a ha) (factor_bounded w n b hb)
  have hq := prod_bounded _ (factor w n c hc) _ _ _ _ _ _ hp
    (factor_bounded w n c hc)
  have hm := map_bounded _ (tripleFactorEquiv a b c)
    (fun p => (((tripleFactorEquiv a b c) p,8),8)) (fun _ => rfl)
    _ _ _ 8 8 hq (fun _ => le_rfl) (fun _ => le_rfl)
  intro stream cursor
  have ht := hm stream cursor
  change _ ≤ factorWork n a+factorWork n b+factorWork n c+20 ∧
    _ ≤ 4*n^3+256 ∧ _ ≤ 3*n^3+136
  exact ⟨ht.1.trans (by omega),ht.2.1.trans (by omega),ht.2.2.trans (by omega)⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
