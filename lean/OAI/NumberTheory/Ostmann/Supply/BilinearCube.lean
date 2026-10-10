import OAI.NumberTheory.Ostmann.Characters.PolynomialCircleEstimate

namespace OAI

/-! # Coefficients of a finite product of bilinear factors -/

namespace Ostmann
open scoped Classical BigOperators

abbrev BilinearCube (n : ℕ) := Fin n → Bool × Bool

def cubeDegree {n : ℕ} (t : BilinearCube n) (b : Bool) : ℕ :=
  ∑ i, if (if b then (t i).2 else (t i).1) then 1 else 0

theorem cubeDegree_le {n : ℕ} (t : BilinearCube n) (b : Bool) : cubeDegree t b ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (by intro i _; split_ifs <;> omega)
    _ = n := by simp

noncomputable def cubeCoefficient {n : ℕ} {E : Type*} [AddCommMonoid E]
    (A : BilinearCube n → E) (i j : ℕ) : E :=
  ∑ t ∈ Finset.univ.filter (fun t => (cubeDegree t false, cubeDegree t true) = (i, j)), A t

theorem cubeCoefficient_polynomial {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (A : BilinearCube n → E) (u v : ℂ) :
    finitePolynomial₂ (cubeCoefficient A) (n + 1) u v =
      ∑ t : BilinearCube n, (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
  unfold finitePolynomial₂ finitePolynomial cubeCoefficient
  simp_rw [Finset.smul_sum, smul_smul]
  calc
    _ = ∑ d ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ∑ t ∈ Finset.univ.filter (fun t => (cubeDegree t false, cubeDegree t true) = d),
          (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t ht
      have he := (Finset.mem_filter.mp ht).2
      have h₁ : cubeDegree t false = i := congrArg Prod.fst he
      have h₂ : cubeDegree t true = j := congrArg Prod.snd he
      rw [h₁, h₂]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro t _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t false)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t true))⟩

theorem cube_power_product {n : ℕ} (t : BilinearCube n) (b : Bool) (u : ℂ) :
    (∏ i, if (if b then (t i).2 else (t i).1) then u else 1) = u ^ cubeDegree t b := by
  unfold cubeDegree
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem bilinear_product_expansion {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (u v : ℂ) :
    (∏ i, (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true))) =
      finitePolynomial₂ (cubeCoefficient (fun t => ∏ i, W i (t i))) (n + 1) u v := by
  rw [cubeCoefficient_polynomial]
  have hl (i : Fin n) : (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true)) =
      ∑ b : Bool × Bool, (if b.1 then u else 1) * (if b.2 then v else 1) * W i b := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    ring
  simp_rw [hl]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h₁ : (∏ i, if (t i).1 then u else 1) = u ^ cubeDegree t false := by
    simpa only [Bool.false_eq_true, ite_false] using cube_power_product t false u
  have h₂ : (∏ i, if (t i).2 then v else 1) = v ^ cubeDegree t true := by
    simpa only [ite_true] using cube_power_product t true v
  rw [h₁, h₂]
  rfl

end Ostmann

end OAI
