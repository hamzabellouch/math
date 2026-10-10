import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Preliminaries.Residues

namespace OAI

/-!
# Separation of square-root populations at split primes

At the end of §3, the squarefree kernels give equations for the two
populations. A square root of their ratio rescales the second population.
The prime-sum exclusion then forces the rescaled residue supports apart.
-/

namespace Ostmann

/-- The algebraic part of the split-prime support separation. -/
theorem disjoint_scaled_root_images {p : ℕ} [Fact p.Prime]
    (A₀ B₀ : Finset ℕ) (r s : ℕ → ℕ) (m u v h c : ZMod p)
    (hm : m ≠ 0) (hscale : u * c ^ 2 = v)
    (hA : ∀ a ∈ A₀, u * (r a : ZMod p) ^ 2 = m * (a : ZMod p) - h)
    (hB : ∀ b ∈ B₀, v * (s b : ZMod p) ^ 2 = m * (-(b : ZMod p)) - h)
    (havoid : ∀ a ∈ A₀, ∀ b ∈ B₀, ¬ p ∣ a + b) :
    Disjoint (A₀.image (fun a => (r a : ZMod p)))
      (B₀.image (fun b => c * (s b : ZMod p))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hzB
  have hsquare : u * (r a : ZMod p) ^ 2 = v * (s b : ZMod p) ^ 2 := by
    rw [← heq, mul_pow, ← mul_assoc, hscale]
  have hsum : m * ((a : ZMod p) + (b : ZMod p)) = 0 := by
    linear_combination hsquare - hA a ha + hB b hb
  have hzero : ((a + b : ℕ) : ZMod p) = 0 := by
    simpa only [Nat.cast_add] using (mul_eq_zero.mp hsum).resolve_left hm
  exact havoid a ha b hb ((ZMod.natCast_eq_zero_iff (a + b) p).mp hzero)

/-- Eventual prime sums supply the required exclusion at every smaller
prime, with the same threshold for all root populations. -/
theorem EventuallyPrimeSumset.disjoint_scaled_root_images {A B : Set ℕ}
    (hprime : EventuallyPrimeSumset A B) :
    ∃ N, ∀ (p : ℕ) (_hp : p.Prime) (A₀ B₀ : Finset ℕ) (r s : ℕ → ℕ)
      (m u v h c : ZMod p),
      m ≠ 0 → u * c ^ 2 = v →
      (∀ a ∈ A₀, a ∈ A) → (∀ b ∈ B₀, b ∈ B) →
      (∀ a ∈ A₀, ∀ b ∈ B₀, N ≤ a + b ∧ p < a + b) →
      (∀ a ∈ A₀, u * (r a : ZMod p) ^ 2 = m * (a : ZMod p) - h) →
      (∀ b ∈ B₀, v * (s b : ZMod p) ^ 2 = m * (-(b : ZMod p)) - h) →
      Disjoint (A₀.image (fun a => (r a : ZMod p)))
        (B₀.image (fun b => c * (s b : ZMod p))) := by
  classical
  obtain ⟨N, hN⟩ := hprime.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp A₀ B₀ r s m u v h c hm hscale hA hB hlarge hkernelA hkernelB
  let : Fact p.Prime := ⟨hp⟩
  apply Ostmann.disjoint_scaled_root_images A₀ B₀ r s m u v h c hm hscale hkernelA hkernelB
  intro a ha b hb
  exact hN p hp a (hA a ha) b (hB b hb) (hlarge a ha b hb).1 (hlarge a ha b hb).2

end Ostmann

end OAI
