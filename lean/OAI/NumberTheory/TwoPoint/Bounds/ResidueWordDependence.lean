import OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability
import OAI.NumberTheory.TwoPoint.Walks.SelectedWitnesses

namespace OAI

/-! The actual attached-word residue tests depend only on their tuple singleton primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- Positivity for a word attached at a fixed displacement from the main origin. -/
def AttachedResiduePositiveWord {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (attachment : ℤ) (B : ℕ) (x : ι → Fin B) : Prop :=
  ∀ (k : Fin w.length) (i : ι),
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) =
        -((attachment + wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))

lemma divisor_prime_in_word_support (w : List SignedStep) (p : ℕ) (hp : p.Prime)
    (hsq : ∀ t ∈ w, Squarefree t.tuple) (hpad : ∀ t ∈ w, ¬p ∣ t.padding)
    (k : Fin w.length) (hk : p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors) :
    p ∈ wordPrimeSupport w := by
  have ht : w.get k ∈ w := List.get_mem w k
  have hd := (Nat.mem_primeFactors.mp hk).2.1
  have hdt : p ∣ (w.get k).tuple := (hp.dvd_mul.mp hd).resolve_left (hpad _ ht)
  exact (mem_wordPrimeSupport p w).mpr
    ⟨w.get k, ht, Nat.mem_primeFactors.mpr ⟨hp, hdt, (hsq _ ht).ne_zero⟩⟩

/-- Freeze all other coordinates, including every padding prime. -/
lemma attached_residue_test_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ) (h B : ℕ) (w : List SignedStep) (attachment : ℤ)
    (hsq : ∀ t ∈ w, Squarefree t.tuple)
    (hprime : ∀ i ∈ S, (p i).Prime) (hpad : ∀ i ∈ S, ∀ t ∈ w, ¬p i ∣ t.padding)
    (outside : {i // i ∉ S} → Fin B) :
    DependsOn (wordCoordinateSupport (fun i : S => p i) w)
      (fun z : S → Fin B => decide (AttachedResiduePositiveWord p h w attachment B
        (joinCoordinates S z outside))) := by
  intro z z' hzz
  apply decide_eq_decide.mpr
  have he (k : Fin w.length) (i : ι)
      (hi : p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors) :
      joinCoordinates S z outside i = joinCoordinates S z' outside i := by
    by_cases his : i ∈ S
    · have hpw := divisor_prime_in_word_support w (p i) (hprime i his) hsq (hpad i his) k hi
      have hz := hzz ⟨i, his⟩ (mem_filter.mpr ⟨mem_univ _, hpw⟩)
      simpa only [joinCoordinates, his, dite_true] using hz
    · simp only [joinCoordinates, his, dite_false]
  constructor
  · intro hz k i hi
    rw [← he k i hi]
    exact hz k i hi
  · intro hz k i hi
    rw [he k i hi]
    exact hz k i hi

end TwoPointCorrelations

end OAI
