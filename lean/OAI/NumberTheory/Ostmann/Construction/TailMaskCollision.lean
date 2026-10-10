import OAI.NumberTheory.Ostmann.ZeroDensity.TailDensityMask
import OAI.NumberTheory.Ostmann.Construction.MaskedPhaseGiantMean

namespace OAI

/-! # The actual tail projection in the giant collision estimate -/

namespace Ostmann
open scoped Classical BigOperators

private theorem tailSupport_cast_injective (A : Set ℕ) (N p : ℕ) :
    Set.InjOn (fun r : ℕ => (r : ZMod p)) (tailSupport A N p) := by
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem sum_tailDensityMask (A : Set ℕ) (N p : ℕ) (f : ZMod p → ℝ) :
    (∑ x ∈ tailDensityMask A N p, f x) =
      ∑ r ∈ tailSupport A N p, f (r : ZMod p) := by
  exact Finset.sum_image (tailSupport_cast_injective A N p)

noncomputable def zmodResidueMass (E : Finset ℕ) (μ : ℕ → ℝ)
    (p : ℕ) (x : ZMod p) : ℝ := residueMass E μ p x.val

theorem tailDensityMask_collision_le {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N p : ℕ) (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (μ ν : ℕ → ℝ) :
    (∑ x ∈ tailDensityMask A N p,
      (zmodResidueMass E μ p x - 1 / ((tailDensityMask A N p).card : ℝ)) ^ 2) ≤
      tailCollisionDefect A N p E D μ ν := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  rw [sum_tailDensityMask, tailDensityMask_card]
  have hs : (∑ r ∈ tailSupport A N p,
      (zmodResidueMass E μ p (r : ZMod p) - 1 / ((tailSupport A N p).card : ℝ)) ^ 2) =
      ∑ r ∈ tailSupport A N p,
        (residueMass E μ p r - 1 / ((tailSupport A N p).card : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    simp only [zmodResidueMass, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]
  rw [hs]
  have hS := tailSupport_nonempty hA N p hp
  have hT := tailSupport_complement_nonempty hB hp hdisjoint
  have hgap := four_div_le_inverse_add_inverse
    (show (0 : ℝ) < (tailSupport A N p).card by exact_mod_cast hS.card_pos)
    (show (0 : ℝ) < (Finset.range p \ tailSupport A N p).card by exact_mod_cast hT.card_pos)
    (show ((tailSupport A N p).card : ℝ) +
      (Finset.range p \ tailSupport A N p).card ≤ p by
      exact_mod_cast (tailSupport_card_add_complement A N p).le)
  have hother : 0 ≤ ∑ r ∈ Finset.range p \ tailSupport A N p,
      (fiberMass D ν (negativeResidue p) r -
        1 / ((Finset.range p \ tailSupport A N p).card : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  dsimp only [tailCollisionDefect, collisionDefect]
  linarith

/-- Projection to the actual finite mask preserves the endpoint average.
No distributional approximation occurs in this identity. -/
theorem tailDensityMask_empirical_mean (A : Set ℕ) (N p : ℕ) (hp : 0 < p)
    (E : Finset ℕ) (μ : ℕ → ℝ) (F : ZMod p → ℝ)
    (hE : ∀ a ∈ E, a ∈ A ∧ N + p < a) :
    (∑ x ∈ tailDensityMask A N p, zmodResidueMass E μ p x * F x) =
      ∑ a ∈ E, μ a * F (a : ZMod p) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  rw [sum_tailDensityMask]
  have hs : (∑ r ∈ tailSupport A N p, zmodResidueMass E μ p (r : ZMod p) * F r) =
      ∑ r ∈ tailSupport A N p, residueMass E μ p r * F r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    simp only [zmodResidueMass, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]
  rw [hs]
  have hh := sum_fiberMass_mul E (tailSupport A N p) μ (fun a => a % p)
    (fun r => F (r : ZMod p)) (fun a ha => mod_mem_tailSupport hp (hE a ha).1 (hE a ha).2)
  simpa only [residueMass, ZMod.natCast_mod] using hh

/-- Logarithmic collision stability also controls any smaller prime weights,
including the localized harmonic weights in a giant cell family. -/
theorem tailDensityMask_weighted_collision {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdisjoint : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (μ ν : ℕ → ℝ) (w : P → ℝ) (G C : ℝ)
    (hG : 0 < G)
    (hweight : ∀ p : P, w p * (p : ℝ) ≤ Real.log (p : ℝ) / G)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) ≤ C) :
    (∑ p : P, w p * ((p : ℝ) * ∑ x ∈ tailDensityMask A N p,
      (zmodResidueMass E μ p x - 1 / ((tailDensityMask A N p).card : ℝ)) ^ 2)) ≤ C / G := by
  have hb : (∑ p : P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) ≤ C := by
    exact (Finset.sum_coe_sort P (fun p : ℕ =>
      Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν)).trans_le hbudget
  calc
    _ ≤ ∑ p : P, (Real.log (p : ℝ) / G) * tailCollisionDefect A N p E D μ ν := by
      apply Finset.sum_le_sum
      intro p _
      have he := tailDensityMask_collision_le hA hB N p (hP p p.property).pos
        (hdisjoint p p.property) E D μ ν
      rw [← mul_assoc]
      exact mul_le_mul (hweight p) he
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_nonneg (Real.log_natCast_nonneg _) hG.le)
    _ = (∑ p : P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) / G := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    _ ≤ C / G := div_le_div_of_nonneg_right hb hG.le

end Ostmann

end OAI
