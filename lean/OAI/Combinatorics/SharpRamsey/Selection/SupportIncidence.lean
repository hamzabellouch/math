import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryLevels
import OAI.Combinatorics.SharpRamsey.Exposure.SupportMixtures

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

lemma good_pairing_eq_event (p : Law A) (q : Law B) (S : Finset A) (T : Finset B)
    (R : A → B → Prop) :
    SupportMixtures.pairing (fun a => if a ∈ S then p.mass a else 0)
      (fun b => if b ∈ T then q.mass b else 0) (fun a b => if R a b then 1 else 0) =
    (p.prod q).event (univ.filter (fun z => z.1 ∈ S ∧ z.2 ∈ T ∧ R z.1 z.2)) := by
  simp only [SupportMixtures.pairing, Law.event, sum_filter, Fintype.sum_prod_type, Law.prod]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ T <;> by_cases hR : R a b <;>
    simp [ha, hb, hR]

lemma auxiliary_good_mixture (p : Law A) (good : Finset A) (M K : ℝ)
    (ρ : Law (retainedLevels p good M K))
    (hρ : ∀ a, (∑ b : retainedLevels p good M K, ρ.mass b *
      (if a ∈ levelSet p b ∩ good then 1 / ((levelSet p b ∩ good).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a) :
    ∀ a, SupportMixtures.mixture ρ.mass (fun b => levelSet p b ∩ good) a ≤
      (4 * exp 1) * (if a ∈ good then p.mass a else 0) := by
  intro a
  by_cases ha : a ∈ good
  · simpa only [ite_eq_left ha, SupportMixtures.mixture, SupportMixtures.kernel] using hρ a
  · simp [SupportMixtures.mixture, SupportMixtures.kernel, ha]

theorem actual_auxiliary_incidence (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MA MB K : ℝ)
    (ρ : Law (retainedLevels p goodA MA K))
    (τ : Law (retainedLevels q goodB MB K))
    (hρ : ∀ a, (∑ b : retainedLevels p goodA MA K, ρ.mass b *
      (if a ∈ levelSet p b ∩ goodA then 1 / ((levelSet p b ∩ goodA).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a)
    (hτ : ∀ a, (∑ b : retainedLevels q goodB MB K, τ.mass b *
      (if a ∈ levelSet q b ∩ goodB then 1 / ((levelSet q b ∩ goodB).card : ℝ) else 0))
      ≤ 4 * exp 1 * q.mass a)
    (R : A → B → Prop) :
    (∑ a, ∑ b, ρ.mass a * τ.mass b *
      (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
        (fun z => R z.1 z.2)).card : ℝ) /
        (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card))) ≤
      (4 * exp 1)^2 * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := SupportMixtures.independent_pairing_le ρ.mass τ.mass
    (fun b => levelSet p b ∩ goodA) (fun b => levelSet q b ∩ goodB)
    (fun a b => if R a b then (1:ℝ) else 0)
    (fun a => if a ∈ goodA then p.mass a else 0)
    (fun b => if b ∈ goodB then q.mass b else 0)
    (4 * exp 1) (4 * exp 1) ρ.nonneg τ.nonneg (by intros; split_ifs <;> norm_num)
    (auxiliary_good_mixture p goodA MA K ρ hρ)
    (auxiliary_good_mixture q goodB MB K τ hτ)
  simpa only [SupportMixtures.kernel_incidence, good_pairing_eq_event, pow_two] using H

lemma pairing_reverse (f : A → ℝ) (g : B → ℝ) (R : A → B → ℝ) :
    SupportMixtures.pairing f g R =
      SupportMixtures.pairing g f (fun b a => R a b) := by
  unfold SupportMixtures.pairing
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  rw [mul_comm (f a)]

theorem actual_auxiliary_target_left (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MA K : ℝ)
    (ρ : Law (retainedLevels p goodA MA K))
    (hρ : ∀ a, (∑ b : retainedLevels p goodA MA K, ρ.mass b *
      (if a ∈ levelSet p b ∩ goodA then 1 / ((levelSet p b ∩ goodA).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a)
    (R : A → B → Prop) :
    (∑ b, ρ.mass b * SupportMixtures.pairing
      (SupportMixtures.kernel (levelSet p b ∩ goodA))
      (fun y => if y ∈ goodB then q.mass y else 0)
      (fun a y => if R a y then 1 else 0)) ≤
      (4 * exp 1) * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := SupportMixtures.one_sided_pairing_le ρ.mass
    (fun b => levelSet p b ∩ goodA)
    (fun a => if a ∈ goodA then p.mass a else 0)
    (fun y => if y ∈ goodB then q.mass y else 0)
    (fun a y => if R a y then (1:ℝ) else 0) (4 * exp 1) ρ.nonneg
    (by intro y; split_ifs <;> simp [q.nonneg])
    (by intros; split_ifs <;> norm_num)
    (auxiliary_good_mixture p goodA MA K ρ hρ)
  simpa only [good_pairing_eq_event] using H

theorem actual_auxiliary_target_right (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MB K : ℝ)
    (τ : Law (retainedLevels q goodB MB K))
    (hτ : ∀ a, (∑ b : retainedLevels q goodB MB K, τ.mass b *
      (if a ∈ levelSet q b ∩ goodB then 1 / ((levelSet q b ∩ goodB).card : ℝ) else 0))
      ≤ 4 * exp 1 * q.mass a)
    (R : A → B → Prop) :
    (∑ b, τ.mass b * SupportMixtures.pairing
      (fun a => if a ∈ goodA then p.mass a else 0)
      (SupportMixtures.kernel (levelSet q b ∩ goodB))
      (fun a y => if R a y then 1 else 0)) ≤
      (4 * exp 1) * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := actual_auxiliary_target_left q p goodB goodA MB K τ hτ (fun b a => R a b)
  rw [← good_pairing_eq_event q p goodB goodA (fun b a => R a b)] at H
  rw [pairing_reverse (fun b => if b ∈ goodB then q.mass b else 0)] at H
  have he (b : retainedLevels q goodB MB K) :
      SupportMixtures.pairing (SupportMixtures.kernel (levelSet q b ∩ goodB))
        (fun a => if a ∈ goodA then p.mass a else 0)
        (fun y a => if R a y then (1:ℝ) else 0) =
      SupportMixtures.pairing (fun a => if a ∈ goodA then p.mass a else 0)
        (SupportMixtures.kernel (levelSet q b ∩ goodB))
        (fun a y => if R a y then (1:ℝ) else 0) := pairing_reverse _ _ _
  simpa only [he, good_pairing_eq_event] using H

end
end SharpLogRamsey.Selection

end

end OAI
