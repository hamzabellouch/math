import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryFamilies

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

lemma Law.prod_left_sum (p : Law A) (q : Law B) (f : A → ℝ) :
    (∑ z, (p.prod q).mass z * f z.1) = ∑ a, p.mass a * f a := by
  simp only [Law.prod, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [←sum_mul, ←mul_sum, q.total, mul_one]

lemma Law.prod_right_sum (p : Law A) (q : Law B) (f : B → ℝ) :
    (∑ z, (p.prod q).mass z * f z.2) = ∑ b, q.mass b * f b := by
  simp only [Law.prod, Fintype.sum_prod_type, mul_assoc, ←mul_sum,
    ←sum_mul, p.total, one_mul]

namespace AuxiliarySupport
variable {p : I → Law A} {q : J → Law B} {goodA : I → Finset A}
  {goodB : J → Finset B} {MA κA : I → ℝ} {MB κB : J → ℝ}

lemma familyLaw_first_sum
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (f : Finset A → ℝ) :
    (∑ z, (familyLaw X Y).mass z * f (z.1 i)) = ∑ S, (X i).setLaw.mass S * f S := by
  rw [familyLaw, Law.prod_left_sum (Law.pi (fun i => (X i).setLaw))
    (Law.pi (fun j => (Y j).setLaw)) (fun z : I → Finset A => f (z i))]
  exact Law.pi_coordinate_sum _ i f

lemma familyLaw_second_sum
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (j : J) (f : Finset B → ℝ) :
    (∑ z, (familyLaw X Y).mass z * f (z.2 j)) = ∑ S, (Y j).setLaw.mass S * f S := by
  rw [familyLaw, Law.prod_right_sum (Law.pi (fun i => (X i).setLaw))
    (Law.pi (fun j => (Y j).setLaw)) (fun z : J → Finset B => f (z j))]
  exact Law.pi_coordinate_sum _ j f

lemma familyLaw_first_density
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) (i : I) (a : A) :
    (∑ z, (familyLaw X Y).mass z * kernel (z.1 i) a) ≤
      (4*exp 1) * (if a ∈ goodA i then (p i).mass a else 0) := by
  rw [familyLaw_first_sum X Y i (fun S => kernel S a)]
  exact (X i).setLaw_density a

lemma familyLaw_second_density
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) (j : J) (b : B) :
    (∑ z, (familyLaw X Y).mass z * kernel (z.2 j) b) ≤
      (4*exp 1) * (if b ∈ goodB j then (q j).mass b else 0) := by
  rw [familyLaw_second_sum X Y j (fun S => kernel S b)]
  exact (Y j).setLaw_density b

lemma familyLaw_first_target
    {T : Type*} [Fintype T] (r : Law T) (goodT : Finset T)
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (R : A → T → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.1 i))
      (fun b => if b ∈ goodT then r.mass b else 0) (fun a b => if R a b then 1 else 0)) ≤
      (4*exp 1) * ((p i).prod r).event
        (univ.filter (fun z => z.1 ∈ goodA i ∧ z.2 ∈ goodT ∧ R z.1 z.2)) := by
  have h := one_sided_pairing_le (familyLaw X Y).mass (fun z => z.1 i)
    (fun a => if a ∈ goodA i then (p i).mass a else 0)
    (fun b => if b ∈ goodT then r.mass b else 0)
    (fun a b => if R a b then (1:ℝ) else 0) (4*exp 1)
    (familyLaw X Y).nonneg (by intro b; split_ifs <;> simp [r.nonneg])
    (by intros; split_ifs <;> norm_num) (familyLaw_first_density X Y i)
  simpa only [good_pairing_eq_event] using h

lemma familyLaw_second_target
    {T : Type*} [Fintype T] (r : Law T) (goodT : Finset T)
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (j : J) (R : B → T → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.2 j))
      (fun b => if b ∈ goodT then r.mass b else 0) (fun a b => if R a b then 1 else 0)) ≤
      (4*exp 1) * ((q j).prod r).event
        (univ.filter (fun z => z.1 ∈ goodB j ∧ z.2 ∈ goodT ∧ R z.1 z.2)) := by
  have h := one_sided_pairing_le (familyLaw X Y).mass (fun z => z.2 j)
    (fun a => if a ∈ goodB j then (q j).mass a else 0)
    (fun b => if b ∈ goodT then r.mass b else 0)
    (fun a b => if R a b then (1:ℝ) else 0) (4*exp 1)
    (familyLaw X Y).nonneg (by intro b; split_ifs <;> simp [r.nonneg])
    (by intros; split_ifs <;> norm_num) (familyLaw_second_density X Y j)
  simpa only [good_pairing_eq_event] using h

end AuxiliarySupport
end
end SharpLogRamsey.Selection

end

end OAI
