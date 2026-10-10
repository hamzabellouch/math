import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasuredRejection
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimitives
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimeTestExecution

namespace OAI

/-! # Concrete measured range and prime seed generation

The cached modulus is an input scalar. The range evaluator is a comparison;
the prime evaluator explicitly computes its powers and then runs the scalar
trial-division cursor. Its charge includes both executed power loops.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

def rangeTest (D : ℕ) (p : Fin (2^Nat.clog 2 D)) : (Bool × ℕ) × ℕ :=
  ((decide (rangeEligible D p),2),8)

def primeTest (ell : ℕ) (p : Fin (2^ell)) : (Bool × ℕ) × ℕ :=
  WordSeedPrimeTestExecution.run ell p

theorem primeTest_value (ell : ℕ) (p : Fin (2^ell)) :
    (primeTest ell p).1.1 = true ↔ primeEligible ell p := by
  rw [primeTest,WordSeedPrimeTestExecution.run_value]
  exact SamplerAttempts.primeTest_correct ell p

theorem primeTest_work (ell : ℕ) (p : Fin (2^ell)) :
    (primeTest ell p).1.2 ≤ 12*2^((ell+1)/2)+12*(ell+1) := by
  exact WordSeedPrimeTestExecution.run_work ell p

theorem primeTest_cells (ell : ℕ) (p : Fin (2^ell)) :
    (primeTest ell p).2 = 28 := by
  exact WordSeedPrimeTestExecution.run_cells ell p

def range (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w)
    (modulus : ℕ) (hm : modulus = 2^Nat.clog 2 D) :
    Execution (WordSeedRealization.range w n D hD hw) := by
  let : Nonempty (Fin D) := ⟨⟨0,by omega⟩⟩
  let : Nonempty {x : Fin (2^Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0,by omega⟩⟩
  exact map
    (rejection (rangeEligible D) (rangeTest D) (fun _ => by
      simp only [rangeTest,decide_eq_true_eq]) hw modulus hm (n^3))
    (rangeEligibleEquiv D) (fun a => (((rangeEligibleEquiv D) a,2),2)) (fun _ => rfl)

theorem range_bounded (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w)
    (modulus : ℕ) (hm : modulus = 2^Nat.clog 2 D) :
    (range w n D hD hw modulus hm).Bounded (13*n^3+15) (2*n^3+96) (n^3+18) := by
  let : Nonempty (Fin D) := ⟨⟨0,by omega⟩⟩
  let : Nonempty {x : Fin (2^Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0,by omega⟩⟩
  have hr := rejection_bounded (rangeEligible D) (rangeTest D)
    (fun _ => by simp only [rangeTest,decide_eq_true_eq]) hw modulus hm
    (n^3) 2 8 (fun _ => le_rfl) (fun _ => le_rfl)
  have h := map_bounded _ (rangeEligibleEquiv D)
    (fun a => (((rangeEligibleEquiv D) a,2),2)) (fun _ => rfl)
    _ _ _ 2 2 hr (fun _ => le_rfl) (fun _ => le_rfl)
  intro stream cursor
  have hh := h stream cursor
  dsimp only [range]
  exact ⟨by omega,hh.2.1.trans (by omega),by omega⟩

def prime (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w)
    (modulus : ℕ) (hm : modulus = 2^ell) :
    Execution (WordSeedRealization.prime w n ell hell hw) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2^ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  exact map (rejection (primeEligible ell) (primeTest ell) (primeTest_value ell)
    hw modulus hm (n^3)) (primeEligibleEquiv hell)
      (fun a => (((primeEligibleEquiv hell) a,2),2)) (fun _ => rfl)

theorem prime_bounded (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w)
    (modulus : ℕ) (hm : modulus = 2^ell) :
    (prime w n ell hell hw modulus hm).Bounded
      (n^3*(12*2^((ell+1)/2)+12*(ell+1)+11)+15) (2*n^3+116) (n^3+18) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2^ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  have hr := rejection_bounded (primeEligible ell) (primeTest ell) (primeTest_value ell)
    hw modulus hm (n^3) _ 28 (primeTest_work ell) (fun p => (primeTest_cells ell p).le)
  have h := map_bounded _ (primeEligibleEquiv hell)
    (fun a => (((primeEligibleEquiv hell) a,2),2)) (fun _ => rfl)
    _ _ _ 2 2 hr (fun _ => le_rfl) (fun _ => le_rfl)
  intro stream cursor
  have hh := h stream cursor
  dsimp only [prime]
  exact ⟨by omega,hh.2.1.trans (by omega),by omega⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
