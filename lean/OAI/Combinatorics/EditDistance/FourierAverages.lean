import OAI.Combinatorics.EditDistance.PrimeCharacters

namespace OAI

/-!
# Uniform averages and quadratic displacement on finite groups
-/

namespace EditFourier
open scoped BigOperators
open Finset

noncomputable def quadraticVariation {R : Type*} [AddCommGroup R] [Fintype R]
    (F : R → ℂ) (l : R) : ℝ :=
  (∑ t, ‖F (t + l) - F t‖ ^ 2) / (Fintype.card R : ℝ)

section Torus
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]

lemma torus_variation_single (F : (∀ j, ZMod (p j)) → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (Pi.single i u) =
      ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        ‖ZMod.stdAddChar (lam i * u) - 1‖ ^ 2 := by
  rw [quadraticVariation, displacement_normalized _ (torusCharacter_primitive p)]
  apply sum_congr rfl
  intro lam _
  rw [mul_comm (Pi.single i u) lam]
  rw [show torusCharacter p (lam * Pi.single i u) = ZMod.stdAddChar (lam i * u) from
    productCharacter_single (fun j => ZMod.stdAddChar (N := p j)) lam i u]

lemma torus_variation_average (F : (∀ j, ZMod (p j)) → ℂ) (i : J) :
    (∑ u : ZMod (p i), quadraticVariation F (Pi.single i u)) /
        (Fintype.card (ZMod (p i)) : ℝ) =
      ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        (if lam i = 0 then (0 : ℝ) else 2) := by
  simp_rw [torus_variation_single p F i]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro lam _
  rw [← mul_sum, mul_div_assoc, average_character_multiplier _ (ZMod.isPrimitive_stdAddChar _)]

theorem torus_quadratic_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (F : (∀ j, ZMod (p j)) → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (Pi.single i u) ≤
      B ^ (2 * h) * quadraticVariation F 1 + (2 / (h : ℝ)) *
        ∑ j, (∑ a : ZMod (p j), quadraticVariation F (Pi.single j a)) /
          (Fintype.card (ZMod (p j)) : ℝ) := by
  rw [torus_variation_single p]
  calc
    _ ≤ ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        (B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 +
          (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2)) := by
      apply sum_le_sum
      intro lam _
      exact mul_le_mul_of_nonneg_left
        (multiplier_comparison p hcop B hB hpB h hh lam i u) (sq_nonneg _)
    _ = _ := by
      simp_rw [torus_variation_average p, quadraticVariation,
        displacement_normalized _ (torusCharacter_primitive p), one_mul,
        mul_add, sum_add_distrib]
      congr 1
      · simp_rw [mul_left_comm _ (B ^ (2 * h)), ← mul_sum]
      · simp_rw [mul_left_comm _ (2 / (h : ℝ)), ← mul_sum, mul_sum]
        rw [sum_comm]

end Torus
end EditFourier

namespace EditAverage
open scoped BigOperators
open Finset

noncomputable def avg {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

lemma avg_nonneg {X : Type*} [Fintype X] {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ avg f := div_nonneg (sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)

lemma avg_mono {X : Type*} [Fintype X] {f g : X → ℝ} (hf : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := div_le_div_of_nonneg_right (sum_le_sum (fun x _ => hf x)) (Nat.cast_nonneg _)

lemma avg_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    avg (fun _ : X => c) = c := by
  simp [avg, Fintype.card_ne_zero]

lemma avg_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    avg (f + g) = avg f + avg g := by simp only [avg, Pi.add_apply, sum_add_distrib, add_div]

lemma avg_mul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    avg (fun x => c * f x) = c * avg f := by rw [avg, ← mul_sum, mul_div_assoc]; rfl

lemma avg_sum {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun x => ∑ y, f x y) = ∑ y, avg (fun x => f x y) := by
  simp only [avg, ← sum_div]
  rw [sum_comm]

lemma avg_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun x => avg (f x)) = avg (fun y => avg (fun x => f x y)) := by
  simp only [avg, ← sum_div, div_div]
  rw [sum_comm, mul_comm]

lemma avg_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    avg (fun x => f (e x)) = avg f := by
  rw [avg, avg, Fintype.card_congr e, Equiv.sum_comp]

lemma avg_shift {G : Type*} [AddGroup G] [Fintype G] (f : G → ℝ) (g : G) :
    avg (fun z => f (z + g)) = avg f := avg_equiv (Equiv.addRight g) f

end EditAverage

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

section Group
variable {G R : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup R] [Fintype R]

lemma quadraticVariation_eq_avg (F : G → ℂ) (l : G) :
    quadraticVariation F l = avg (fun t => ‖F (t + l) - F t‖ ^ 2) := rfl

lemma quadraticVariation_pullback_average (φ : R →+ G) (F : G → ℂ) (l : R) :
    avg (fun c : G => quadraticVariation (fun t : R => F (c + φ t)) l) =
      quadraticVariation F (φ l) := by
  simp_rw [quadraticVariation_eq_avg, map_add, ← add_assoc]
  rw [avg_comm]
  have hshift (t : R) :
      avg (fun c : G => ‖F (c + φ t + φ l) - F (c + φ t)‖ ^ 2) =
        avg (fun c : G => ‖F (c + φ l) - F c‖ ^ 2) :=
    avg_shift (fun c : G => ‖F (c + φ l) - F c‖ ^ 2) (φ t)
  simp_rw [hshift]
  exact avg_const _

end Group

section TorusGroup
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem group_quadratic_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (φ : (∀ j, ZMod (p j)) →+ G)
    (F : G → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (φ (Pi.single i u)) ≤
      B ^ (2 * h) * quadraticVariation F (φ 1) + (2 / (h : ℝ)) *
        ∑ j, avg (fun a : ZMod (p j) => quadraticVariation F (φ (Pi.single j a))) := by
  have hpoint (c : G) := torus_quadratic_comparison p hcop B hB hpB h hh
    (fun t => F (c + φ t)) i u
  have havg := avg_mono hpoint
  change avg (fun c : G => quadraticVariation (fun t => F (c + φ t)) (Pi.single i u)) ≤
    avg (fun c : G => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1 +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) at havg
  rw [show (fun c : G => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1 +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) =
    (fun c => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1) +
    (fun c => (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) from rfl,
    avg_add] at havg
  simp_rw [avg_mul, avg_sum, avg_comm (fun c a =>
    quadraticVariation (fun t => F (c + φ t)) (Pi.single _ a)),
    quadraticVariation_pullback_average] at havg
  exact havg

end TorusGroup
end EditFourier

end OAI
