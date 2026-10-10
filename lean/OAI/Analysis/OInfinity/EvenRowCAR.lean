import OAI.Analysis.OInfinity.CARShiftModes

namespace OAI

/-! # The CAR seed of a finite even Cuntz row

The given row is indexed by `Fin 2 × Fin n`. Its two equal blocks supply
matrix units with corner unit `q`, even when the row has more than two
members. The resulting seed commutes with the actual row shift.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] {n : ℕ}

def evenRowMatrixUnit (r : Fin 2 × Fin n → E) (α β : Fin 2) : E :=
  ∑ i, r (α, i) * star (r (β, i))

def evenRowShift (r : Fin 2 × Fin n → E) (x : E) : E :=
  ∑ p, r p * x * star (r p)

def evenRowSeed (r : Fin 2 × Fin n → E) : E := evenRowMatrixUnit r 0 1

def evenRowParity (r : Fin 2 × Fin n → E) : E :=
  evenRowMatrixUnit r 0 0 - evenRowMatrixUnit r 1 1

def evenRowCAR (r : Fin 2 × Fin n → E) : ℕ → E
  | 0 => evenRowSeed r
  | k + 1 => evenRowParity r * evenRowShift r (evenRowCAR r k)

lemma evenRowMatrixUnit_star (r : Fin 2 × Fin n → E) (α β : Fin 2) :
    star (evenRowMatrixUnit r α β) = evenRowMatrixUnit r β α := by
  simp only [evenRowMatrixUnit, star_sum, star_mul, star_star]

lemma evenRowShift_star (r : Fin 2 × Fin n → E) (x : E) :
    star (evenRowShift r x) = evenRowShift r (star x) := by
  simp only [evenRowShift, star_sum, star_mul, star_star, mul_assoc]

lemma evenRowShift_add (r : Fin 2 × Fin n → E) (x y : E) :
    evenRowShift r (x + y) = evenRowShift r x + evenRowShift r y := by
  simp only [evenRowShift, mul_add, add_mul, Finset.sum_add_distrib]

lemma evenRowShift_zero (r : Fin 2 × Fin n → E) : evenRowShift r 0 = 0 := by
  simp only [evenRowShift, mul_zero, zero_mul, Finset.sum_const_zero]

section Row
variable (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

include hqstar hqq hrow in
lemma evenRow_right_support (i : Fin 2 × Fin n) : r i * q = r i := by
  have hi : star (r i) * r i = q := by simpa only [ite_true] using hrow i i
  exact relativeIsometry_mul_support (r i) q hi hqstar hqq

include hqstar hqq hrow hsum in
lemma evenRow_left_support (i : Fin 2 × Fin n) : q * r i = r i := by
  rw [← hsum, Finset.sum_mul]
  have hterm (j : Fin 2 × Fin n) :
      (r j * star (r j)) * r i = if j = i then r i else 0 := by
    rw [mul_assoc, hrow]
    split_ifs with h
    · subst j
      exact evenRow_right_support q r hqstar hqq hrow i
    · exact mul_zero _
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hqstar hqq hrow in
lemma evenRowMatrixUnit_mul (α β γ δ : Fin 2) :
    evenRowMatrixUnit r α β * evenRowMatrixUnit r γ δ =
      if β = γ then evenRowMatrixUnit r α δ else 0 := by
  have hterm (i j : Fin n) :
      (r (α, i) * star (r (β, i))) * (r (γ, j) * star (r (δ, j))) =
        if (β, i) = (γ, j) then r (α, i) * star (r (δ, j)) else 0 := by
    calc
      _ = r (α, i) * (star (r (β, i)) * r (γ, j)) * star (r (δ, j)) := by
        simp only [mul_assoc]
      _ = _ := by
        rw [hrow]
        split_ifs with h
        · rw [evenRow_right_support q r hqstar hqq hrow]
        · simp only [mul_zero, zero_mul]
  simp only [evenRowMatrixUnit, Finset.sum_mul, Finset.mul_sum, hterm]
  by_cases hβγ : β = γ
  · subst γ
    simp
  · simp [Prod.mk.injEq, hβγ]

include hsum in
lemma evenRowMatrixUnit_sum : evenRowMatrixUnit r 0 0 + evenRowMatrixUnit r 1 1 = q := by
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, evenRowMatrixUnit] using hsum

include hqstar hqq hrow hsum in
lemma evenRowMatrixUnit_support (α β : Fin 2) :
    q * evenRowMatrixUnit r α β = evenRowMatrixUnit r α β ∧
      evenRowMatrixUnit r α β * q = evenRowMatrixUnit r α β := by
  have hstar (i : Fin 2 × Fin n) : star (r i) * q = star (r i) := by
    simpa only [star_mul, hqstar] using
      congrArg star (evenRow_left_support q r hqstar hqq hrow hsum i)
  constructor
  · simp only [evenRowMatrixUnit, Finset.mul_sum, ← mul_assoc,
      evenRow_left_support q r hqstar hqq hrow hsum]
  · simp only [evenRowMatrixUnit, Finset.sum_mul, mul_assoc, hstar]

include hqstar hqq hrow hsum in
lemma evenRowSeed_relations :
    evenRowSeed r * evenRowSeed r = 0 ∧
      star (evenRowSeed r) * evenRowSeed r + evenRowSeed r * star (evenRowSeed r) = q ∧
      evenRowParity r * evenRowSeed r = -(evenRowSeed r) * evenRowParity r := by
  have hmul := evenRowMatrixUnit_mul q r hqstar hqq hrow
  constructor
  · simp only [evenRowSeed, hmul]
    norm_num
  constructor
  · simp only [evenRowSeed, evenRowMatrixUnit_star, hmul, ite_true]
    rw [add_comm]
    exact evenRowMatrixUnit_sum q r hsum
  · simp only [evenRowSeed, evenRowParity, sub_mul, mul_sub, neg_mul, hmul]
    norm_num

include hqstar hqq hrow hsum in
lemma evenRowParity_relations :
    star (evenRowParity r) = evenRowParity r ∧
      evenRowParity r * evenRowParity r = q ∧
      q * evenRowParity r = evenRowParity r ∧
      evenRowParity r * q = evenRowParity r := by
  have hmul := evenRowMatrixUnit_mul q r hqstar hqq hrow
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evenRowParity, star_sub, evenRowMatrixUnit_star]
  · simp only [evenRowParity, sub_mul, mul_sub, hmul]
    norm_num
    exact evenRowMatrixUnit_sum q r hsum
  · simp only [evenRowParity, mul_sub,
      (evenRowMatrixUnit_support q r hqstar hqq hrow hsum 0 0).1,
      (evenRowMatrixUnit_support q r hqstar hqq hrow hsum 1 1).1]
  · simp only [evenRowParity, sub_mul,
      (evenRowMatrixUnit_support q r hqstar hqq hrow hsum 0 0).2,
      (evenRowMatrixUnit_support q r hqstar hqq hrow hsum 1 1).2]

include hqstar hqq hrow in
lemma evenRowMatrixUnit_mul_row (α β γ : Fin 2) (j : Fin n) :
    evenRowMatrixUnit r α β * r (γ, j) = if β = γ then r (α, j) else 0 := by
  have hterm (i : Fin n) :
      (r (α, i) * star (r (β, i))) * r (γ, j) =
        if (β, i) = (γ, j) then r (α, i) else 0 := by
    rw [mul_assoc, hrow]
    split_ifs with h
    · exact evenRow_right_support q r hqstar hqq hrow _
    · exact mul_zero _
  simp only [evenRowMatrixUnit, Finset.sum_mul, hterm]
  by_cases hβγ : β = γ
  · subst γ
    simp
  · simp [Prod.mk.injEq, hβγ]

include hqstar hqq hrow in
lemma evenRow_star_row_mul_MatrixUnit (α β γ : Fin 2) (j : Fin n) :
    star (r (γ, j)) * evenRowMatrixUnit r α β =
      if γ = α then star (r (β, j)) else 0 := by
  have h := congrArg star (evenRowMatrixUnit_mul_row q r hqstar hqq hrow β α γ j)
  by_cases hαγ : α = γ
  · subst γ
    simpa only [star_mul, evenRowMatrixUnit_star, ite_true] using h
  · have hγα : γ ≠ α := Ne.symm hαγ
    simpa only [star_mul, evenRowMatrixUnit_star, hαγ, hγα, ite_false, star_zero] using h

include hqstar hqq hrow in
lemma evenRowMatrixUnit_commute_shift (α β : Fin 2) (x : E) :
    Commute (evenRowMatrixUnit r α β) (evenRowShift r x) := by
  have hleft : evenRowMatrixUnit r α β * evenRowShift r x =
      ∑ j, r (α, j) * x * star (r (β, j)) := by
    simp only [evenRowShift, Fintype.sum_prod_type, Finset.mul_sum]
    have hterm (γ : Fin 2) (j : Fin n) :
        evenRowMatrixUnit r α β * (r (γ, j) * x * star (r (γ, j))) =
          if β = γ then r (α, j) * x * star (r (γ, j)) else 0 := by
      rw [← mul_assoc, ← mul_assoc,
        evenRowMatrixUnit_mul_row q r hqstar hqq hrow]
      split_ifs <;> simp only [zero_mul]
    simp only [hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hright : evenRowShift r x * evenRowMatrixUnit r α β =
      ∑ j, r (α, j) * x * star (r (β, j)) := by
    simp only [evenRowShift, Fintype.sum_prod_type, Finset.sum_mul]
    have hterm (γ : Fin 2) (j : Fin n) :
        (r (γ, j) * x * star (r (γ, j))) * evenRowMatrixUnit r α β =
          if γ = α then r (γ, j) * x * star (r (β, j)) else 0 := by
      rw [mul_assoc, evenRow_star_row_mul_MatrixUnit q r hqstar hqq hrow]
      split_ifs <;> simp only [mul_zero]
    simp only [hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  exact hleft.trans hright.symm

include hqstar hqq hrow in
lemma evenRowSeed_commute_shift (x : E) : Commute (evenRowSeed r) (evenRowShift r x) := by
  exact evenRowMatrixUnit_commute_shift q r hqstar hqq hrow 0 1 x

include hqstar hqq hrow in
lemma evenRowParity_commute_shift (x : E) : Commute (evenRowParity r) (evenRowShift r x) := by
  exact (evenRowMatrixUnit_commute_shift q r hqstar hqq hrow 0 0 x).sub_left
    (evenRowMatrixUnit_commute_shift q r hqstar hqq hrow 1 1 x)

include hqstar hqq hrow hsum in
lemma evenRowShift_support (x : E) :
    q * evenRowShift r x = evenRowShift r x ∧ evenRowShift r x * q = evenRowShift r x := by
  have hstar (i : Fin 2 × Fin n) : star (r i) * q = star (r i) := by
    simpa only [star_mul, hqstar] using
      congrArg star (evenRow_left_support q r hqstar hqq hrow hsum i)
  constructor
  · simp only [evenRowShift, Finset.mul_sum, ← mul_assoc,
      evenRow_left_support q r hqstar hqq hrow hsum]
  · simp only [evenRowShift, Finset.sum_mul, mul_assoc, hstar]

include hqstar hqq hrow hsum in
lemma evenRowShift_unit : evenRowShift r q = q := by
  simpa only [evenRowShift, evenRow_right_support q r hqstar hqq hrow] using hsum

include hrow in
lemma evenRowShift_mul (x y : E) (hy : q * y = y) :
    evenRowShift r x * evenRowShift r y = evenRowShift r (x * y) := by
  have hterm (i j : Fin 2 × Fin n) :
      (r i * x * star (r i)) * (r j * y * star (r j)) =
        if i = j then r i * (x * y) * star (r i) else 0 := by
    calc
      _ = r i * x * (star (r i) * r j) * y * star (r j) := by simp only [mul_assoc]
      _ = _ := by
        rw [hrow]
        split_ifs with h
        · subst j
          simp only [mul_assoc, hy]
        · simp only [mul_zero, zero_mul]
  simp only [evenRowShift, Finset.sum_mul, Finset.mul_sum, hterm,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hqstar hqq hrow hsum in
lemma evenRowCAR_support : ∀ k,
    q * evenRowCAR r k = evenRowCAR r k ∧ evenRowCAR r k * q = evenRowCAR r k := by
  intro k
  cases k with
  | zero => exact evenRowMatrixUnit_support q r hqstar hqq hrow hsum 0 1
  | succ k =>
    have hp := evenRowParity_relations q r hqstar hqq hrow hsum
    have hs := evenRowShift_support q r hqstar hqq hrow hsum (evenRowCAR r k)
    constructor
    · change q * (evenRowParity r * evenRowShift r (evenRowCAR r k)) =
        evenRowParity r * evenRowShift r (evenRowCAR r k)
      rw [← mul_assoc, hp.2.2.1]
    · change (evenRowParity r * evenRowShift r (evenRowCAR r k)) * q =
        evenRowParity r * evenRowShift r (evenRowCAR r k)
      rw [mul_assoc, hs.2]

end Row
end WeakPureInfiniteness

end

end OAI
