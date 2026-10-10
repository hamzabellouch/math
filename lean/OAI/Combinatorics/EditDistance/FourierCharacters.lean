import Mathlib

namespace OAI

/-!
# Finite Fourier inversion, Parseval, and character displacement
-/

namespace EditFourier
open scoped BigOperators
open Finset

section FiniteRing
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable def transform (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) : ℂ :=
  ∑ t : R, ψ (-(t * k)) * F t

theorem transform_twice (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) :
    transform ψ (transform ψ F) = fun j => (Fintype.card R : ℂ) * F (-j) := by
  funext j
  simp only [transform, mul_sum, ← mul_assoc, ← AddChar.map_add_eq_mul, ← neg_add,
    mul_comm _ j, ← add_mul]
  rw [sum_comm]
  simp only [← sum_mul, ← neg_mul]
  have h1 (t : R) : ∑ i, ψ (t * i) = if t = 0 then (Fintype.card R : ℂ) else 0 := by
    simpa only [mul_comm, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift t hψ
  have h2 (x j : R) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

omit [DecidableEq R] in
theorem transform_sub (ψ : AddChar R ℂ) (F G : R → ℂ) :
    transform ψ (F - G) = transform ψ F - transform ψ G := by
  funext k
  simp only [transform, Pi.sub_apply, mul_sub, sum_sub_distrib]

omit [DecidableEq R] in
theorem transform_shift (ψ : AddChar R ℂ) (F : R → ℂ) (l k : R) :
    transform ψ (fun t => F (t + l)) k = ψ (l * k) * transform ψ F k := by
  classical
  calc
    _ = ∑ t : R, ψ (-((t - l) * k)) * F t := by
      apply Fintype.sum_equiv (Equiv.addRight l)
      intro t
      simp
    _ = ψ (l * k) * transform ψ F k := by
      rw [transform, mul_sum]
      apply sum_congr rfl
      intro t _
      rw [sub_mul, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

omit [DecidableEq R] in
theorem transform_pairing (ψ : AddChar R ℂ) (F G : R → ℂ) :
    ∑ k, transform ψ F k * G k = ∑ t, F t * transform ψ G t := by
  simp only [transform, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro k _
  rw [mul_comm k t]
  ring

omit [DecidableEq R] in
theorem transform_conj (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) :
    transform ψ (fun t => (starRingEnd ℂ) (F t)) k =
      (starRingEnd ℂ) (transform ψ F (-k)) := by
  simp only [transform, map_sum, map_mul]
  apply sum_congr rfl
  intro t _
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

theorem parseval (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) :
    ∑ k, ‖transform ψ F k‖ ^ 2 = (Fintype.card R : ℝ) * ∑ t, ‖F t‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj]
  rw [transform_pairing]
  simp only [transform_conj, transform_twice ψ hψ F, neg_neg, map_mul,
    map_natCast, Finset.mul_sum]
  apply sum_congr rfl
  intro t _
  ring

theorem displacement (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) (l : R) :
    (Fintype.card R : ℝ) * ∑ t, ‖F (t + l) - F t‖ ^ 2 =
      ∑ k, ‖transform ψ F k‖ ^ 2 * ‖ψ (l * k) - 1‖ ^ 2 := by
  rw [← parseval ψ hψ (fun t => F (t + l) - F t)]
  have ht : transform ψ (fun t => F (t + l) - F t) =
      fun k => (ψ (l * k) - 1) * transform ψ F k := by
    rw [show (fun t => F (t + l) - F t) = (fun t => F (t + l)) - F from rfl,
      transform_sub]
    funext k
    simp only [Pi.sub_apply, transform_shift]
    ring
  rw [ht]
  apply sum_congr rfl
  intro k _
  rw [norm_mul, mul_pow, mul_comm]

noncomputable def fourier (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) : ℂ :=
  transform ψ F k / (Fintype.card R : ℂ)

theorem displacement_normalized (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (F : R → ℂ) (l : R) :
    (∑ t, ‖F (t + l) - F t‖ ^ 2) / (Fintype.card R : ℝ) =
      ∑ k, ‖fourier ψ F k‖ ^ 2 * ‖ψ (l * k) - 1‖ ^ 2 := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [fourier, norm_div, Complex.norm_natCast, div_pow, div_mul_eq_mul_div,
    ← sum_div]
  apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
  rw [← displacement ψ hψ F l]
  field_simp

end FiniteRing

section ProductCharacter
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {A : J → Type*} [∀ j, CommRing (A j)]

noncomputable def productCharacter (ψ : ∀ j, AddChar (A j) ℂ) :
    AddChar (∀ j, A j) ℂ where
  toFun x := ∏ j, ψ j (x j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [AddChar.map_add_eq_mul, prod_mul_distrib]

theorem productCharacter_single (ψ : ∀ j, AddChar (A j) ℂ)
    (a : ∀ j, A j) (j : J) (x : A j) :
    (productCharacter ψ) (a * Pi.single j x) = ψ j (a j * x) := by
  change ∏ i, ψ i (a i * Pi.single j x i) = _
  rw [prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

theorem productCharacter_primitive (ψ : ∀ j, AddChar (A j) ℂ)
    (hψ : ∀ j, (ψ j).IsPrimitive) : (productCharacter ψ).IsPrimitive := by
  intro a ha h
  apply ha
  funext j
  by_contra hj
  apply hψ j hj
  ext x
  have hx := DFunLike.congr_fun h (Pi.single j x)
  simpa only [AddChar.mulShift_apply, productCharacter_single, AddChar.one_apply] using hx

noncomputable def torusCharacter (p : J → ℕ) [∀ j, NeZero (p j)] :
    AddChar (∀ j, ZMod (p j)) ℂ :=
  productCharacter (fun j => ZMod.stdAddChar (N := p j))

theorem torusCharacter_primitive (p : J → ℕ) [∀ j, NeZero (p j)] :
    (torusCharacter p).IsPrimitive :=
  productCharacter_primitive _ (fun j => ZMod.isPrimitive_stdAddChar (p j))

end ProductCharacter
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖z ^ (n + 1) - 1‖ = ‖z * (z ^ n - 1) + (z - 1)‖ := by
        congr 1
        rw [pow_succ']
        ring
      _ ≤ ‖z * (z ^ n - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ = ‖z ^ n - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
      _ ≤ (n : ℝ) * ‖z - 1‖ + ‖z - 1‖ := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

theorem root_separation (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (q : ℕ) (hq : 0 < q) (hpow : z ^ q = 1) :
    2 ≤ (q : ℝ) * ‖z - 1‖ := by
  have hs : ∑ i ∈ range q, z ^ i = 0 := by
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr hne.symm)
    rw [mul_neg_geom_sum, hpow, sub_self]
  have heq : (q : ℝ) = ‖∑ i ∈ range q, (1 - z ^ i)‖ := by
    simp [sum_sub_distrib, hs]
  have hbound : (q : ℝ) ≤ (∑ i ∈ range q, (i : ℝ)) * ‖z - 1‖ := by
    rw [heq]
    calc
      _ ≤ ∑ i ∈ range q, ‖1 - z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range q, (i : ℝ) * ‖z - 1‖ := by
        apply sum_le_sum
        intro i _
        rw [norm_sub_rev]
        exact norm_pow_sub_one_le z hz i
      _ = _ := by rw [sum_mul]
  have hid : (∑ i ∈ range q, (i : ℝ)) * 2 = (q : ℝ) * ((q : ℝ) - 1) := by
    have ht := congrArg (fun a : ℕ => (a : ℝ)) (sum_range_id_mul_two q)
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt hq)] at ht
    exact ht
  have hnn := norm_nonneg (z - 1)
  have hm := congrArg (fun x : ℝ => x * ‖z - 1‖) hid
  have hp : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hh : (q : ℝ) * 2 ≤ (q : ℝ) * ((q : ℝ) * ‖z - 1‖) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hp).mp hh

end EditFourier

end OAI
