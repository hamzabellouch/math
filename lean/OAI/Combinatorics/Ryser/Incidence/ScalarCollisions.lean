import OAI.Combinatorics.Ryser.Incidence.RatioSet
import OAI.Combinatorics.Ryser.Incidence.ScalarCollisionCount
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

open scoped BigOperators Pointwise

namespace RyserCoveringCounterexample.Incidence

section Fibers

variable {α β : Type*} [instDecidableEqα : DecidableEq α] [DecidableEq β]

theorem card_collisionPairs_eq_sum_sq (s : Finset α) (f : α → β) :
    ((s.product s).filter (fun p => f p.1 = f p.2)).card =
      ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card ^ 2 := let _ := instDecidableEqα; by
  classical
  let fibers (b : β) := s.filter (fun a => f a = b)
  have hdisj : (s.image f : Set β).PairwiseDisjoint
      (fun b => (fibers b).product (fibers b)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hpb : f p.1 = b :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hpc' : f p.1 = c :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hpc).1).2
    exact hbc (hpb.symm.trans hpc')
  have hpartition :
      (s.product s).filter (fun p => f p.1 = f p.2) =
        (s.image f).disjiUnion (fun b => (fibers b).product (fibers b)) hdisj := by
    ext p
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_disjiUnion, fibers]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hf⟩
      exact ⟨f p.1, Finset.mem_image_of_mem f hp1, ⟨⟨hp1, rfl⟩, ⟨hp2, hf.symm⟩⟩⟩
    · rintro ⟨b, hb, ⟨⟨hp1, hf1⟩, ⟨hp2, hf2⟩⟩⟩
      exact ⟨⟨hp1, hp2⟩, hf1.trans hf2.symm⟩
  rw [hpartition, Finset.card_disjiUnion]
  simp only [Finset.product_eq_sprod, Finset.card_product, fibers, pow_two]

theorem card_sq_le_card_image_mul_collisionPairs (s : Finset α) (f : α → β) :
    s.card ^ 2 ≤ (s.image f).card *
      ((s.product s).filter (fun p => f p.1 = f p.2)).card := by
  calc
    s.card ^ 2 = (∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card) ^ 2 := by
      rw [← Finset.card_eq_sum_card_image f s]
    _ ≤ (s.image f).card *
        ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) (s.image f)
        (fun _ => 1) (fun b => (s.filter (fun a => f a = b)).card)
    _ = _ := by rw [← card_collisionPairs_eq_sum_sq s f]

end Fibers

variable {F : Type*} [Field F] [DecidableEq F]

theorem image_scalar_add (E : Finset F) (c : F) :
    (E.product E).image (fun p : F × F => p.1 + c * p.2) = dilateSum E c := by
  ext z
  simp only [dilateSum, Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
    Finset.mem_add]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    exact ⟨x, hx, c * y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨x, hx, z, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hxy⟩

theorem dilateSum_eq_add_smul (E : Finset F) (c : F) :
    dilateSum E c = E + c • E := rfl

theorem card_dilateSum_mul_scalarCollisionCount (E : Finset F) (c : F) :
    E.card ^ 4 ≤ (dilateSum E c).card * scalarCollisionCount E c := by
  have h := card_sq_le_card_image_mul_collisionPairs (E.product E)
    (fun p : F × F => p.1 + c * p.2)
  rw [image_scalar_add E c] at h
  simp only [Finset.product_eq_sprod, Finset.card_product] at h
  simpa only [scalarCollisionCount, Finset.product_eq_sprod, pow_two, pow_succ, pow_zero,
    mul_one, mul_assoc] using h

variable [Fintype F]

theorem card_field_lt_twice_of_dilateSum_card_le_real (E : Finset F) (U : ℝ)
    (hU0 : 0 ≤ U) (hU : ∀ c : F, ((dilateSum E c).card : ℝ) ≤ U)
    (hsmall : 2 * U < (E.card : ℝ) ^ 2) : (Fintype.card F : ℝ) < 2 * U := by
  have hcauchy (c : F) : (E.card : ℝ) ^ 4 ≤
      ((dilateSum E c).card : ℝ) * (scalarCollisionCount E c : ℝ) := by
    exact_mod_cast card_dilateSum_mul_scalarCollisionCount E c
  have hsum : (Fintype.card F : ℝ) * (E.card : ℝ) ^ 4 ≤
      U * ∑ c : F, (scalarCollisionCount E c : ℝ) := by
    calc
      _ = ∑ _c : F, (E.card : ℝ) ^ 4 := by simp
      _ ≤ ∑ c : F, U * (scalarCollisionCount E c : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact (hcauchy c).trans
          (mul_le_mul_of_nonneg_right (hU c) (Nat.cast_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htotal : (∑ c : F, (scalarCollisionCount E c : ℝ)) + (E.card : ℝ) ^ 3 =
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 + (E.card : ℝ) ^ 4 := by
    exact_mod_cast sum_scalarCollisionCount E
  have htotal_le : (∑ c : F, (scalarCollisionCount E c : ℝ)) ≤
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 + (E.card : ℝ) ^ 4 := by
    have hcube : 0 ≤ (E.card : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hupper := mul_le_mul_of_nonneg_left htotal_le hU0
  have hqpos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hEpos : 0 < (E.card : ℝ) ^ 2 :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) hU0) hsmall
  by_contra hnot
  have hq : 2 * U ≤ (Fintype.card F : ℝ) := le_of_not_gt hnot
  have h₁ := mul_le_mul_of_nonneg_right hq (sq_nonneg (E.card : ℝ))
  have h₂ := mul_lt_mul_of_pos_right hsmall hqpos
  have hgap : U * (Fintype.card F : ℝ) + U * (E.card : ℝ) ^ 2 <
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 := by nlinarith
  have hstrict := mul_lt_mul_of_pos_right hgap hEpos
  nlinarith

theorem card_field_lt_twice_of_dilateSum_card_le (E : Finset F) (U : ℕ)
    (hU : ∀ c : F, (dilateSum E c).card ≤ U) (hsmall : 2 * U < E.card ^ 2) :
    Fintype.card F < 2 * U := by
  have h := card_field_lt_twice_of_dilateSum_card_le_real E (U : ℝ)
    (Nat.cast_nonneg _) (fun c => by exact_mod_cast hU c) (by exact_mod_cast hsmall)
  exact_mod_cast h

end RyserCoveringCounterexample.Incidence

end OAI
