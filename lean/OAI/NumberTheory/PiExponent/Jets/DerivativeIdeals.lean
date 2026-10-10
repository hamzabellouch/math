import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic
import OAI.NumberTheory.PiExponent.Approximation.PersistentComponents

namespace OAI

noncomputable section
namespace PiExponent.DerivativeIdeals

variable {C R ι : Type*} [CommRing C] [CommRing R] [Algebra C R]

def wordDerivative (D : ι → Derivation C R R) (word : List ι) (f : R) : R :=
  word.foldr (fun i g => D i g) f

@[simp] theorem wordDerivative_nil (D : ι → Derivation C R R) (f : R) :
    wordDerivative D [] f = f := rfl

@[simp] theorem wordDerivative_cons (D : ι → Derivation C R R) (i : ι)
    (word : List ι) (f : R) : wordDerivative D (i :: word) f = D i (wordDerivative D word f) := rfl

def wordCost (cost : ι → ℝ) (word : List ι) : ℝ := (word.map cost).sum

@[simp] theorem wordCost_nil (cost : ι → ℝ) : wordCost cost [] = 0 := rfl
@[simp] theorem wordCost_cons (cost : ι → ℝ) (i : ι) (word : List ι) :
    wordCost cost (i :: word) = cost i + wordCost cost word := rfl

theorem wordCost_nonneg (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i) (word : List ι) :
    0 ≤ wordCost cost word := by
  induction word with
  | nil => exact le_refl 0
  | cons i word ih => exact add_nonneg (hcost i) ih

def derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ) (bound : ℝ) (f : R) :
    Ideal R := Ideal.span {g | ∃ word, wordCost cost word ≤ bound ∧ wordDerivative D word f = g}

theorem word_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (bound : ℝ) (f : R) (word : List ι) (hw : wordCost cost word ≤ bound) :
    wordDerivative D word f ∈ derivativeIdeal D cost bound f :=
  Ideal.subset_span ⟨word, hw, rfl⟩

theorem derivativeIdeal_mono (D : ι → Derivation C R R) (cost : ι → ℝ)
    (f : R) {a b : ℝ} (hab : a ≤ b) :
    derivativeIdeal D cost a f ≤ derivativeIdeal D cost b f := by
  apply Ideal.span_mono
  rintro g ⟨word, hw, rfl⟩
  exact ⟨word, hw.trans hab, rfl⟩

theorem self_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (bound : ℝ) (f : R) (hb : 0 ≤ bound) : f ∈ derivativeIdeal D cost bound f :=
  word_mem_derivativeIdeal D cost bound f [] hb

def derivativeCore (D : Derivation C R R) (I : Ideal R) : Ideal R where
  carrier := {f | f ∈ I ∧ D f ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨I.add_mem hf.1 hg.1, ?_⟩
    rw [map_add]
    exact I.add_mem hf.2 hg.2
  smul_mem' := by
    intro r f hf
    change r * f ∈ I ∧ D (r * f) ∈ I
    refine ⟨I.mul_mem_left r hf.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hf.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hf.1)

theorem derivation_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (i : ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    D i g ∈ derivativeIdeal D cost (bound + cost i) f := by
  let I := derivativeIdeal D cost (bound + cost i) f
  have hle : derivativeIdeal D cost bound f ≤ derivativeCore (D i) I := by
    apply Ideal.span_le.mpr
    rintro g ⟨word, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f word
        (hw.trans (le_add_of_nonneg_right (hcost i)))
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f (i :: word)
        (by simpa only [wordCost_cons, add_comm] using add_le_add_left hw (cost i))
  exact (hle hg).2

theorem wordDerivative_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (word : List ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    wordDerivative D word g ∈ derivativeIdeal D cost (bound + wordCost cost word) f := by
  induction word with
  | nil => simpa only [wordDerivative_nil, wordCost_nil, add_zero] using hg
  | cons i word ih =>
    have h := derivation_mem_derivativeIdeal D cost hcost
      (bound + wordCost cost word) f (wordDerivative D word g) i ih
    simpa only [wordDerivative_cons, wordCost_cons, add_assoc,
      add_comm (wordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal (D : ι → Derivation C R R)
    (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i) (bound delta : ℝ) (f g : R)
    (Q : Ideal R) (hg : g ∈ derivativeIdeal D cost bound f)
    (hpersist : derivativeIdeal D cost (bound + delta) f ≤ Q)
    (word : List ι) (hw : wordCost cost word ≤ delta) :
    wordDerivative D word g ∈ Q := by
  apply hpersist
  have hb : bound + wordCost cost word ≤ bound + delta := by linarith
  exact derivativeIdeal_mono D cost f hb
    (wordDerivative_mem_derivativeIdeal D cost hcost bound f g word hg)

theorem derivativeIdeal_levels_monotone (D : ι → Derivation C R R) (cost : ι → ℝ)
    (delta : ℝ) (hdelta : 0 ≤ delta) (f : R) :
    Monotone (fun r : ℕ => derivativeIdeal D cost ((r : ℝ) * delta) f) := by
  intro a b hab
  exact derivativeIdeal_mono D cost f
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hdelta)

theorem exists_persistent_derivative_component [IsDomain R]
    (D : ι → Derivation C R R) (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (f : R) (hf : f ≠ 0)
    (d : ℕ) (P : Ideal R) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ word : List ι, wordCost cost word ≤ ((d : ℝ) + 2) * delta →
      wordDerivative D word f ∈ P) :
    ∃ r < d + 2, ∃ Q : Ideal R,
      Q ∈ (derivativeIdeal D cost ((r : ℝ) * delta) f).minimalPrimes ∧
      Q ∈ (derivativeIdeal D cost (((r : ℝ) + 1) * delta) f).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ d ∧
      ∀ g ∈ derivativeIdeal D cost ((r : ℝ) * delta) f,
        ∀ word : List ι, wordCost cost word ≤ delta → wordDerivative D word g ∈ Q := by
  let I : ℕ → Ideal R := fun r => derivativeIdeal D cost ((r : ℝ) * delta) f
  have hI : Monotone I := derivativeIdeal_levels_monotone D cost delta hdelta f
  have htop : I (d + 2) ≤ P := by
    apply Ideal.span_le.mpr
    rintro g ⟨word, hw, rfl⟩
    apply hvanish word
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hw
  have hinitial : f ∈ I 0 := by
    simpa only [I, Nat.cast_zero, zero_mul] using self_mem_derivativeIdeal D cost 0 f (le_refl 0)
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi⟩ :=
    PiExponent.PersistentComponents.exists_persistent_component_positive_height
      I hI d P hP htop hheight hf hinitial
  refine ⟨r, hr, Q, hQr, ?_, hQP, hQlo, hQhi, ?_⟩
  · simpa only [I, Nat.cast_add, Nat.cast_one] using hQnext
  · intro g hg word hw
    apply derivative_vanishes_on_persistent_ideal D cost hcost
      ((r : ℝ) * delta) delta f g Q hg
    · have hb : (r : ℝ) * delta + delta = ((r + 1 : ℕ) : ℝ) * delta := by
        push_cast
        ring
      rw [hb]
      exact hQnext.le
    · exact hw

end PiExponent.DerivativeIdeals
end

end OAI
