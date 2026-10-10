import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

namespace OAI

/-!
# Finite coordinate packing

Rounding coordinates embeds a separated set into a finite integer box. This
provides explicit cardinal bounds for polynomially bounded matrix coordinates,
without any measurability assumption on the set of path endpoints.
-/

namespace PolycyclicRecognition

/-- Integer boxes count separated points in a bounded coordinate box. -/
theorem card_le_integer_grid {X I : Type*} [Fintype I]
    (s : Finset X) (f : X → I → ℝ) (N : ℕ)
    (hbox : ∀ x ∈ s, ∀ i, -(N : ℝ) ≤ f x i ∧ f x i < (N : ℝ) + 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, 1 ≤ |f x i - f y i|) :
    s.card ≤ (2 * N + 1) ^ Fintype.card I := by
  classical
  let code : {x // x ∈ s} → (I → Set.Icc (-(N : ℤ)) (N : ℤ)) := fun x i =>
    ⟨⌊f x.val i⌋, by
      constructor
      · apply Int.le_floor.mpr
        simpa using (hbox x.val x.property i).1
      · have h : ⌊f x.val i⌋ < (N : ℤ) + 1 := Int.floor_lt.mpr (by
          simpa using (hbox x.val x.property i).2)
        omega⟩
  have hc : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x.val x.property y.val y.property hne
    have heq : ⌊f x.val i⌋ = ⌊f y.val i⌋ := congrArg Subtype.val (congrFun hxy i)
    exact (not_lt_of_ge hi) (Int.abs_sub_lt_one_of_floor_eq_floor heq)
  have hcard := Fintype.card_le_of_injective code hc
  have hIcc : Fintype.card (Set.Icc (-(N : ℤ)) (N : ℤ)) = 2 * N + 1 := by
    rw [Fintype.card_Icc, Int.card_Icc]
    omega
  simpa only [Fintype.card_coe, Fintype.card_fun, hIcc] using hcard

/-- Scaling a coordinate box gives the corresponding fixed-separation bound. -/
theorem card_le_scaled_grid {X I : Type*} [Fintype I]
    (s : Finset X) (f : X → I → ℝ) {δ R : ℝ} (hδ : 0 < δ)
    (N : ℕ) (hN : R / δ ≤ N)
    (hbox : ∀ x ∈ s, ∀ i, |f x i| ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, δ ≤ |f x i - f y i|) :
    s.card ≤ (2 * N + 1) ^ Fintype.card I := by
  apply card_le_integer_grid s (fun x i => f x i / δ) N
  · intro x hx i
    have hb : |f x i / δ| ≤ (N : ℝ) := by
      rw [abs_div, abs_of_pos hδ]
      exact (div_le_div_of_nonneg_right (hbox x hx i) hδ.le).trans hN
    exact ⟨(abs_le.mp hb).1, lt_of_le_of_lt (abs_le.mp hb).2 (by linarith)⟩
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hsep x hx y hy hxy
    refine ⟨i, ?_⟩
    rw [← sub_div, abs_div, abs_of_pos hδ]
    exact (le_div_iff₀ hδ).mpr (by simpa using hi)

/-- Polynomially bounded coordinate boxes contain only polynomially many
points with unit coordinate separation. -/
theorem card_le_polynomial_grid {X I : Type*} [Fintype I]
    (s : Finset X) (f : X → I → ℝ) (A b t : ℕ)
    (hbox : ∀ x ∈ s, ∀ i, |f x i| ≤ ((A * (1 + t) ^ b : ℕ) : ℝ))
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, 1 ≤ |f x i - f y i|) :
    s.card ≤ (2 * A + 1) ^ Fintype.card I * (1 + t) ^ (b * Fintype.card I) := by
  have h := card_le_integer_grid s f (A * (1 + t) ^ b) (by
    intro x hx i
    have hb := abs_le.mp (hbox x hx i)
    exact ⟨hb.1, lt_of_le_of_lt hb.2 (by linarith)⟩) hsep
  apply h.trans
  have hq : 1 ≤ (1 + t) ^ b := Nat.one_le_pow _ _ (by omega)
  have hbase : 2 * (A * (1 + t) ^ b) + 1 ≤ (2 * A + 1) * (1 + t) ^ b := by
    nlinarith
  calc
    _ ≤ ((2 * A + 1) * (1 + t) ^ b) ^ Fintype.card I := Nat.pow_le_pow_left hbase (Fintype.card I)
    _ = _ := by rw [mul_pow, ← pow_mul]

end PolycyclicRecognition

end OAI
