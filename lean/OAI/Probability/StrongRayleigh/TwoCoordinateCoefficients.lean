import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14

noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem336AdditiveD139

def twoCoordinateCoefficient {F : Type u_1} [Fintype F]
    (weight : (F → Bool) → ℂ) (i j : F) (r : F → ℂ) (p q : Bool) : ℂ := by
  classical
  exact ∑ x : F → Bool, if x i = p ∧ x j = q then
    weight x * ∏ k ∈ (Finset.univ.erase i).erase j,
      if x k = true then r k else 1
    else 0

lemma binary_pair_sum {X : Type u_2} [Fintype X]
    (u v : X → Bool) (f : X → ℂ) :
    (∑ x, f x) =
      (∑ x, if u x = false ∧ v x = false then f x else 0) +
      (∑ x, if u x = true ∧ v x = false then f x else 0) +
      (∑ x, if u x = false ∧ v x = true then f x else 0) +
      (∑ x, if u x = true ∧ v x = true then f x else 0) := by
  classical
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases u x <;> cases v x <;> simp

def twoCoordinateField {F : Type u_3} (i j : F) (r : F → ℂ) (z w : ℂ) : F → ℂ := by
  classical
  exact fun k => if k = i then z else if k = j then w else r k

lemma monomial_two_coordinates {F : Type u_4} [Fintype F]
    (x : F → Bool) (r : F → ℂ) (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∏ k : F, if x k = true then twoCoordinateField i j r z w k else 1) =
    (if x i = true then z else 1) * (if x j = true then w else 1) *
      ∏ k ∈ (Finset.univ.erase i).erase j, if x k = true then r k else 1 := by
  classical
  let f : F → ℂ := fun k => if x k = true then twoCoordinateField i j r z w k else 1
  have hi : i ∈ (Finset.univ : Finset F) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset F).erase i := by simp [hij.symm]
  change (∏ k, f k) = _
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hj]
  have hprod : (∏ k ∈ (Finset.univ.erase i).erase j, f k) =
      ∏ k ∈ (Finset.univ.erase i).erase j, if x k = true then r k else 1 := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [f, twoCoordinateField, hki, hkj]
  rw [hprod]
  simp [f, twoCoordinateField, hij.symm, mul_assoc]

lemma weighted_generating_two_coordinates {F : Type u_5} [Fintype F]
    (weight : (F → Bool) → ℂ) (r : F → ℂ) (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∑ x : F → Bool, weight x *
      ∏ k : F, if x k = true then twoCoordinateField i j r z w k else 1) =
    twoCoordinateCoefficient weight i j r false false +
      twoCoordinateCoefficient weight i j r true false * z +
      twoCoordinateCoefficient weight i j r false true * w +
      twoCoordinateCoefficient weight i j r true true * z * w := by
  classical
  simp only [twoCoordinateCoefficient, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [monomial_two_coordinates x r i j hij z w]
  cases hxi : x i <;> cases hxj : x j <;> simp <;> ring

lemma finiteGeneratingValue_two_coordinates {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (r : F → ℂ)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    finiteGeneratingValue μ (twoCoordinateField i j r z w) =
    twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r false false +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r true false * z +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r false true * w +
      twoCoordinateCoefficient (fun x => (((μ : Measure (F → Bool)) {x}).toReal : ℂ))
        i j r true true * z * w := by
  classical
  exact weighted_generating_two_coordinates _ r i j hij z w

lemma continuous_twoCoordinateCoefficient {F : Type u_7} [Fintype F]
    (weight : (F → Bool) → ℂ) (i j : F) (p q : Bool) :
    Continuous (fun r : F → ℂ => twoCoordinateCoefficient weight i j r p q) := by
  unfold twoCoordinateCoefficient
  apply continuous_finsetSum
  intro x hx
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetProd
    intro k hk
    split_ifs <;> fun_prop
  · exact continuous_const

def twoCoordinateWeight {F : Type u_8} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (p q : Bool) : ℝ :=
  ∑ x : F → Bool, if x i = p ∧ x j = q then weight x else 0

lemma twoCoordinateWeight_total {F : Type u_9} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x) =
      twoCoordinateWeight weight i j false false +
      twoCoordinateWeight weight i j true false +
      twoCoordinateWeight weight i j false true +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp

lemma twoCoordinateWeight_first {F : Type u_10} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x i)) =
      twoCoordinateWeight weight i j true false +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma twoCoordinateWeight_second {F : Type u_11} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x j)) =
      twoCoordinateWeight weight i j false true +
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma twoCoordinateWeight_both {F : Type u_12} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) :
    (∑ x, weight x * boolReal (x i) * boolReal (x j)) =
      twoCoordinateWeight weight i j true true := by
  simp only [twoCoordinateWeight]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> cases x j <;> simp [boolReal]

lemma binary_covariance_eq_pair_determinant {F : Type u_13} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (hZ : (∑ x, weight x) ≠ 0) :
    (∑ x, weight x * boolReal (x i) * boolReal (x j)) / (∑ x, weight x) -
      ((∑ x, weight x * boolReal (x i)) / (∑ x, weight x)) *
      ((∑ x, weight x * boolReal (x j)) / (∑ x, weight x)) =
    (twoCoordinateWeight weight i j false false * twoCoordinateWeight weight i j true true -
      twoCoordinateWeight weight i j true false * twoCoordinateWeight weight i j false true) /
      (∑ x, weight x) ^ 2 := by
  rw [twoCoordinateWeight_first weight i j, twoCoordinateWeight_second weight i j,
    twoCoordinateWeight_both weight i j]
  have htotal := twoCoordinateWeight_total weight i j
  field_simp
  rw [htotal]
  ring

lemma twoCoordinateWeight_cast_eq_coefficient {F : Type u_14} [Fintype F]
    (weight : (F → Bool) → ℝ) (i j : F) (p q : Bool) :
    (twoCoordinateWeight weight i j p q : ℂ) =
      twoCoordinateCoefficient (fun x => (weight x : ℂ)) i j (fun _ => 1) p q := by
  simp only [twoCoordinateWeight, twoCoordinateCoefficient, Complex.ofReal_sum,
    ite_self, Finset.prod_const_one, mul_one]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

end Problem336AdditiveD139

end

end OAI
