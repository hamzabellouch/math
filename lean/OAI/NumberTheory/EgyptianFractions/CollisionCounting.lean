import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Ordered pairs with equal images, including the diagonal. -/
def collisionPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) : Finset (α × α) :=
  (A ×ˢ A).filter (fun p => f p.1 = f p.2)

/-- Ordered collisions between distinct inputs. -/
def strictCollisionPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) : Finset (α × α) :=
  (collisionPairs A f).filter (fun p => p.1 ≠ p.2)

lemma collision_card_eq_sum_square {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    (collisionPairs A f).card = ∑ y ∈ A.image f, (A.filter (fun a => f a = y)).card ^ 2 := by
  have hmaps : (collisionPairs A f : Set (α × α)).MapsTo
      (fun p => f p.1) (A.image f) := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro y hy
  have hf : (collisionPairs A f).filter (fun p => f p.1 = y) =
      (A.filter (fun a => f a = y)) ×ˢ (A.filter (fun a => f a = y)) := by
    ext p
    simp only [collisionPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [hf, Finset.card_product, pow_two]

lemma collision_card_eq_strict_add {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    (collisionPairs A f).card = (strictCollisionPairs A f).card + A.card := by
  have hdiag : (collisionPairs A f).filter (fun p => ¬p.1 ≠ p.2) = A.diag := by
    ext p
    simp only [collisionPairs, Finset.mem_filter, Finset.mem_product, not_not,
      Finset.mem_diag]
    aesop
  have h := Finset.card_filter_add_card_filter_not (s := collisionPairs A f)
    (fun p => p.1 ≠ p.2)
  rw [hdiag, Finset.diag_card] at h
  exact h.symm

/-- Cauchy--Schwarz lower bound for the number of collisions of a finite map. -/
theorem card_sq_le_image_card_mul_collisions {α β : Type*} [DecidableEq α]
    [DecidableEq β] (A : Finset α) (f : α → β) :
    A.card ^ 2 ≤ (A.image f).card * ((strictCollisionPairs A f).card + A.card) := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := A.image f) (f := fun y => (A.filter (fun a => f a = y)).card)
  rw [← Finset.card_eq_sum_card_image f A, ← collision_card_eq_sum_square,
    collision_card_eq_strict_add] at h
  exact h

/-- If the image has at most half as many elements as the domain, the
strict collisions retain at least half the Cauchy--Schwarz lower bound. -/
theorem strict_collision_lower_bound {α β : Type*} [DecidableEq α]
    [DecidableEq β] (A : Finset α) (f : α → β) {H : ℝ} (hH : 0 < H)
    (himage : ((A.image f).card : ℝ) ≤ H) (hsize : 2 * H ≤ (A.card : ℝ)) :
    (A.card : ℝ) ^ 2 / (2 * H) ≤ ((strictCollisionPairs A f).card : ℝ) := by
  have hcs : (A.card : ℝ) ^ 2 ≤ ((A.image f).card : ℝ) *
      (((strictCollisionPairs A f).card : ℝ) + (A.card : ℝ)) := by
    exact_mod_cast card_sq_le_image_card_mul_collisions A f
  have hc : 0 ≤ ((strictCollisionPairs A f).card : ℝ) + (A.card : ℝ) := by positivity
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_right himage hc)
  have hmul := mul_nonneg (show 0 ≤ (A.card : ℝ) by positivity)
    (sub_nonneg.mpr hsize)
  apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
  nlinarith

/-- A generic larger-sieve counting step. A family of maps with small images
is small when no distinct pair collides in too many maps. The codomain is
allowed to depend on the map (as it does for reduction modulo varying primes). -/
theorem exceptional_maps_card_le {ι α : Type*} {β : ι → Type*}
    [DecidableEq ι] [DecidableEq α] [∀ i, DecidableEq (β i)]
    (I : Finset ι) (A : Finset α) (f : ∀ i, α → β i)
    {H B : ℝ} (hH : 0 < H) (hB : 0 ≤ B)
    (hsize : 2 * H ≤ (A.card : ℝ))
    (himage : ∀ i ∈ I, ((A.image (f i)).card : ℝ) ≤ H)
    (hpairs : ∀ p ∈ A.offDiag,
      ((I.filter (fun i => f i p.1 = f i p.2)).card : ℝ) ≤ B) :
    (I.card : ℝ) ≤ 2 * H * B := by
  classical
  have hlow : ∀ i ∈ I, (A.card : ℝ)^2 / (2 * H) ≤
      ((A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i).card : ℝ) := by
    intro i hi
    have heq : A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i =
        strictCollisionPairs A (f i) := by
      ext p
      simp only [Finset.mem_bipartiteAbove, Finset.mem_offDiag,
        strictCollisionPairs, collisionPairs, Finset.mem_filter, Finset.mem_product]
      tauto
    rw [heq]
    exact strict_collision_lower_bound A (f i) hH (himage i hi) hsize
  have hdouble := Finset.card_nsmul_le_card_nsmul
    (R := ℝ) (s := I) (t := A.offDiag)
    (m := (A.card : ℝ)^2 / (2 * H)) (n := B)
    (fun (i : ι) (p : α × α) => f i p.1 = f i p.2) hlow hpairs
  simp only [nsmul_eq_mul] at hdouble
  have hoffnat : A.offDiag.card ≤ A.card ^ 2 := by
    calc
      A.offDiag.card ≤ (A ×ˢ A).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hp).1,
          (Finset.mem_offDiag.mp hp).2.1⟩)
      _ = A.card ^ 2 := by rw [Finset.card_product, pow_two]
  have hoff : (A.offDiag.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by exact_mod_cast hoffnat
  have hbound := hdouble.trans (mul_le_mul_of_nonneg_right hoff hB)
  have hmain : (I.card : ℝ) * (A.card : ℝ)^2 ≤
      (A.card : ℝ)^2 * B * (2 * H) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mp
    simpa only [mul_div_assoc] using hbound
  have hN : 0 < (A.card : ℝ) := by linarith
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp
  calc
    (I.card : ℝ) * (A.card : ℝ)^2 ≤ (A.card : ℝ)^2 * B * (2 * H) := hmain
    _ = (2 * H * B) * (A.card : ℝ)^2 := by ring

/-- The number of distinct prime factors of a positive integer is at most
its base-two logarithm. -/
theorem primeFactors_card_le_log_collision {d : ℕ} (hd : 0 < d) :
    (d.primeFactors.card : ℝ) ≤ Real.log (d : ℝ) / Real.log 2 := by
  have hpow : 2 ^ d.primeFactors.card ≤ d := by
    calc
      2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 :=
        (Finset.prod_const 2).symm
      _ ≤ ∏ p ∈ d.primeFactors, p := Finset.prod_le_prod
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ d := Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  have hpowR : (2 : ℝ) ^ d.primeFactors.card ≤ (d : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ d.primeFactors.card) hpowR
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

/-- Distinct positive integers below `P` collide modulo at most `log₂ P`
primes, even when the tested prime set has no prescribed size. -/
theorem prime_mod_collision_card_le (I : Finset ℕ) {a b P : ℕ}
    (hprime : ∀ p ∈ I, p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (haP : a ≤ P) (hbP : b ≤ P) (hab : a ≠ b) :
    ((I.filter (fun p => a % p = b % p)).card : ℝ) ≤
      Real.log (P : ℝ) / Real.log 2 := by
  have hd : 0 < Nat.dist a b := Nat.dist_pos_of_ne hab
  have hsub : I.filter (fun p => a % p = b % p) ⊆ (Nat.dist a b).primeFactors := by
    intro p hp
    obtain ⟨hpI, hmod⟩ := Finset.mem_filter.mp hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hprime p hpI, ?_, by omega⟩
    have hm : Nat.ModEq p a b := hmod
    rcases le_total a b with hab' | hba'
    · rw [Nat.dist_eq_sub_of_le hab']
      exact (Nat.modEq_iff_dvd' hab').mp hm
    · rw [Nat.dist_eq_sub_of_le_right hba']
      exact (Nat.modEq_iff_dvd' hba').mp hm.symm
  have hcard : ((I.filter (fun p => a % p = b % p)).card : ℝ) ≤
      ((Nat.dist a b).primeFactors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hdP : Nat.dist a b ≤ P := by unfold Nat.dist; omega
  have hlog : Real.log (Nat.dist a b : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdP)
  exact hcard.trans ((primeFactors_card_le_log_collision hd).trans
    (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))))

/-- Exceptional-prime bound underlying the rational-divisor supply. If all
reductions of `A` modulo primes in `I` have size at most `H`, and `|A| ≥ 2H`,
then `|I| ≤ 2H log(P)/log(2)` for `A ⊆ {1,...,P}`. -/
theorem exceptional_primes_card_le (I A : Finset ℕ) (P : ℕ) {H : ℝ}
    (hprime : ∀ p ∈ I, p.Prime) (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P)
    (hP : 1 ≤ P) (hH : 0 < H) (hsize : 2 * H ≤ (A.card : ℝ))
    (himage : ∀ p ∈ I, ((A.image (fun a => a % p)).card : ℝ) ≤ H) :
    (I.card : ℝ) ≤ 2 * H * (Real.log (P : ℝ) / Real.log 2) := by
  apply exceptional_maps_card_le I A (fun p a => a % p) hH
    (div_nonneg (Real.log_nonneg (by exact_mod_cast hP))
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) hsize himage
  intro p hp
  obtain ⟨hpa, hpb, hne⟩ := Finset.mem_offDiag.mp hp
  exact prime_mod_collision_card_le I hprime (hA p.1 hpa).1 (hA p.2 hpb).1
    (hA p.1 hpa).2 (hA p.2 hpb).2 hne

/-- The `u^(3/4)` exceptional-prime estimate in the supply construction,
with all size hypotheses explicit and no analytic prime-distribution input. -/
theorem exceptional_primes_three_quarters (I A : Finset ℕ) (u P : ℕ)
    (hu : 2 ≤ u) (hprime : ∀ p ∈ I, p.Prime ∧ p ≤ u)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P) (hP : 1 ≤ P)
    (hsize : u ^ 4 ≤ A.card)
    (himage : ∀ p ∈ I,
      ((A.image (fun a => a % p)).card : ℝ) ≤ (p : ℝ) ^ (3 / 4 : ℝ)) :
    (I.card : ℝ) ≤ 2 * (u : ℝ) ^ (3 / 4 : ℝ) *
      (Real.log (P : ℝ) / Real.log 2) := by
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hpow : (u : ℝ) ^ (3 / 4 : ℝ) ≤ (u : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hsizeR : (u : ℝ) ^ 4 ≤ (A.card : ℝ) := by exact_mod_cast hsize
  have haux := mul_nonneg (sq_nonneg (u : ℝ))
    (show 0 ≤ (u : ℝ)^2 - 1 by nlinarith)
  apply exceptional_primes_card_le I A P (fun p hp => (hprime p hp).1) hA hP
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < u) _)
    (by nlinarith)
  intro p hp
  exact (himage p hp).trans (Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast (hprime p hp).2) (by norm_num))

end Problem337

end OAI
