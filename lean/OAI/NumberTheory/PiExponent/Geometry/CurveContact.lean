import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.PiExponent.Approximation.PersistentComponents
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame

namespace OAI

namespace PiExponentApprox

noncomputable section

def frameWordCost {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (word : List (Fin (m + 1))) : ℝ := (word.map cost).sum

@[simp] theorem frameWordCost_nil {m : ℕ} (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost [] = 0 := rfl

@[simp] theorem frameWordCost_cons {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (word : List (Fin (m + 1))) :
    frameWordCost cost (i :: word) = cost i + frameWordCost cost word := rfl

theorem frameWordCost_nonneg {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (word : List (Fin (m + 1))) :
    0 ≤ frameWordCost cost word := by
  induction word with
  | nil => exact le_refl 0
  | cons i word ih => exact add_nonneg (hcost i) ih

def frameDerivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) : Ideal (FramePolynomial m) :=
  Ideal.span {g | ∃ word, frameWordCost cost word ≤ bound ∧
    polynomialFrameWord m word F = g}

theorem frameWord_mem_derivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) (word : List (Fin (m + 1)))
    (hword : frameWordCost cost word ≤ bound) :
    polynomialFrameWord m word F ∈ frameDerivativeIdeal cost bound F :=
  Ideal.subset_span ⟨word, hword, rfl⟩

theorem frameDerivativeIdeal_mono {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (F : FramePolynomial m) {a b : ℝ} (hab : a ≤ b) :
    frameDerivativeIdeal cost a F ≤ frameDerivativeIdeal cost b F := by
  apply Ideal.span_mono
  intro g hg
  obtain ⟨word, hword, rfl⟩ := hg
  exact ⟨word, hword.trans hab, rfl⟩

theorem polynomial_mem_frameDerivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (bound : ℝ) (F : FramePolynomial m)
    (hbound : 0 ≤ bound) : F ∈ frameDerivativeIdeal cost bound F :=
  frameWord_mem_derivativeIdeal cost bound F [] hbound

def polynomialDerivativeCore {m : ℕ}
    (D : Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (I : Ideal (FramePolynomial m)) : Ideal (FramePolynomial m) where
  carrier := {p | p ∈ I ∧ D p ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, D.map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨I.add_mem hp.1 hq.1, ?_⟩
    rw [map_add]
    exact I.add_mem hp.2 hq.2
  smul_mem' := by
    intro r p hp
    change r * p ∈ I ∧ D (r * p) ∈ I
    refine ⟨I.mul_mem_left r hp.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hp.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hp.1)

theorem polynomialFrame_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (i : Fin (m + 1))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrame m i p ∈ frameDerivativeIdeal cost (bound + cost i) F := by
  let I := frameDerivativeIdeal cost (bound + cost i) F
  have hle : frameDerivativeIdeal cost bound F ≤
      polynomialDerivativeCore (polynomialFrame m i) I := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F word
        (hword.trans (le_add_of_nonneg_right (hcost i)))
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F (i :: word)
        (by simpa only [frameWordCost_cons, add_comm] using add_le_add_left hword (cost i))
  exact (hle hp).2

theorem polynomialFrameWord_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (word : List (Fin (m + 1)))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrameWord m word p ∈
      frameDerivativeIdeal cost (bound + frameWordCost cost word) F := by
  induction word with
  | nil => simpa only [polynomialFrameWord_nil, frameWordCost_nil, add_zero] using hp
  | cons i word ih =>
      have h := polynomialFrame_mem_derivativeIdeal cost hcost
        (bound + frameWordCost cost word) F (polynomialFrameWord m word p) i ih
      simpa only [polynomialFrameWord_cons, frameWordCost_cons, add_assoc,
        add_comm (frameWordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound delta : ℝ) (F p : FramePolynomial m)
    (P : Ideal (FramePolynomial m))
    (hp : p ∈ frameDerivativeIdeal cost bound F)
    (hpersist : frameDerivativeIdeal cost (bound + delta) F ≤ P)
    (word : List (Fin (m + 1))) (hword : frameWordCost cost word ≤ delta) :
    polynomialFrameWord m word p ∈ P := by
  apply hpersist
  have hbound : bound + frameWordCost cost word ≤ bound + delta := by linarith
  exact frameDerivativeIdeal_mono cost F hbound
    (polynomialFrameWord_mem_derivativeIdeal cost hcost bound F p word hp)

theorem frameDerivativeIdeal_levels_monotone {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) :
    Monotone (fun r : ℕ => frameDerivativeIdeal cost ((r : ℝ) * delta) F) := by
  intro a b hab
  apply frameDerivativeIdeal_mono
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hdelta

theorem exists_persistent_frame_component {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta →
        polynomialFrameWord m word F ∈ P) :
    ∃ r < m + 2, ∃ Q : Ideal (FramePolynomial m),
      Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes ∧
      Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ m ∧
      ∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
        ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
          polynomialFrameWord m word p ∈ Q := by
  let I : ℕ → Ideal (FramePolynomial m) :=
    fun r => frameDerivativeIdeal cost ((r : ℝ) * delta) F
  have hI : Monotone I := frameDerivativeIdeal_levels_monotone cost delta hdelta F
  have htop : I (m + 2) ≤ P := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    apply hvanish word
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hword
  have hinitial : F ∈ I 0 := by
    simpa only [I, Nat.cast_zero, zero_mul] using
      polynomial_mem_frameDerivativeIdeal cost 0 F (le_refl 0)
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi⟩ :=
    PiExponent.PersistentComponents.exists_persistent_component_positive_height
      I hI m P hP htop hheight hF hinitial
  refine ⟨r, hr, Q, hQr, ?_, hQP, hQlo, hQhi, ?_⟩
  · simpa only [I, Nat.cast_add, Nat.cast_one] using hQnext
  · intro p hp word hword
    apply derivative_vanishes_on_persistent_ideal cost hcost
      ((r : ℝ) * delta) delta F p Q hp
    · have hb : (r : ℝ) * delta + delta = ((r + 1 : ℕ) : ℝ) * delta := by
        push_cast
        ring
      rw [hb]
      exact hQnext.le
    · exact hword

end
end PiExponentApprox

end OAI
