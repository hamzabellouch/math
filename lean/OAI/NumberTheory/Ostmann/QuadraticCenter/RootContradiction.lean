import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisions
import OAI.NumberTheory.Ostmann.QuadraticCenter.SplitCollision

namespace OAI

/-!
# Combining the root-population collision bounds

This proves the final finite contradiction in §3 from the populations and
split-prime mass constructed earlier there. Their construction, including
the common rational center, remains a separate part of the argument.
-/

namespace Ostmann

open scoped BigOperators

theorem root_population_scale_bound (P R s t : Finset ℕ)
    (hs : s.Nonempty) (ht : t.Nonempty) (Ds Dt : ℕ)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt)
    (hdiamS : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ Ds)
    (hdiamT : ∀ a ∈ t, ∀ b ∈ t, Nat.dist a b ≤ Dt)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (c : (p : ℕ) → ZMod p) (hc : ∀ p ∈ R, c p ≠ 0)
    (hdisjoint : ∀ p ∈ R,
      Disjoint (s.image (fun a : ℕ => (a : ZMod p)))
        (t.image (fun b : ℕ => c p * (b : ZMod p))))
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (s.card : ℝ) + 1 / (t.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) :
    L ≤ 50 * C := by
  apply split_collision_scale_bound P R (uniformResidueCollision s)
    (uniformResidueCollision t) L η C hRP hP
  · intro p hp
    have hp' := (hP p hp).pos
    calc
      2 / (p : ℝ) = 1 / (p : ℝ) + 1 / (p : ℝ) := by ring
      _ ≤ uniformResidueCollision s p + uniformResidueCollision t p :=
        add_le_add (uniformResidueCollision_lower s hs hp')
          (uniformResidueCollision_lower t ht hp')
  · intro p hp
    let : Fact p.Prime := ⟨hP p (hRP hp)⟩
    exact uniformResidueCollision_lower_of_scaled_disjoint s t hs ht (c p)
      (hc p hp) (hdisjoint p hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · have hS := uniformResidueCollision_upper P s hs Ds hDs hP hdiamS
    have hT := uniformResidueCollision_upper P t ht Dt hDt hP hdiamT
    calc
      _ = (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision s p) +
          (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision t p) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ (Real.log (Ds : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ)) +
          (Real.log (Dt : ℝ) + (1 / (t.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ)) :=
        add_le_add hS hT
      _ ≤ (101 / 100) * L := by linarith

end Ostmann

end OAI
