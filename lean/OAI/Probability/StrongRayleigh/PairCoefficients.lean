import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

def tiltPairMass {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (b c : Bool) : ℝ := by
  classical
  exact ∑ x : F → Bool, if x i = b ∧ x j = c then
    Real.exp (∑ k : F, h k * boolReal (x k)) *
      ((μ : Measure (F → Bool)) {x}).toReal else 0

lemma tiltPairMass_nonneg {F : Type u_2} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (b c : Bool) : 0 ≤ tiltPairMass μ h i j b c := by
  classical
  unfold tiltPairMass
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  · exact le_rfl

lemma tiltPartition_pairMass {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltPartition μ h = tiltPairMass μ h i j false false +
      tiltPairMass μ h i j true false + tiltPairMass μ h i j false true +
      tiltPairMass μ h i j true true := by
  classical
  unfold tiltPartition tiltPairMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp

lemma tiltMean_pairMass_left {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltMean μ h i =
      (tiltPairMass μ h i j true false + tiltPairMass μ h i j true true) /
        tiltPartition μ h := by
  classical
  unfold tiltMean tiltPairMass
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltMean_pairMass_right {F : Type u_5} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltMean μ h j =
      (tiltPairMass μ h i j false true + tiltPairMass μ h i j true true) /
        tiltPartition μ h := by
  classical
  unfold tiltMean tiltPairMass
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltSecondMoment_pairMass {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltSecondMoment μ h i j =
      tiltPairMass μ h i j true true / tiltPartition μ h := by
  classical
  unfold tiltSecondMoment tiltPairMass
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  cases hi : x i <;> cases hj : x j <;> simp [boolReal]

lemma tiltCovariance_pairMass {F : Type u_7} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    tiltCovariance μ h i j =
      (tiltPairMass μ h i j false false * tiltPairMass μ h i j true true -
        tiltPairMass μ h i j true false * tiltPairMass μ h i j false true) /
          (tiltPartition μ h)^2 := by
  rw [tiltCovariance, tiltSecondMoment_pairMass, tiltMean_pairMass_left μ h i j,
    tiltMean_pairMass_right μ h i j]
  by_cases hz : tiltPartition μ h = 0
  · simp [hz]
  · field_simp
    rw [tiltPartition_pairMass μ h i j]
    ring

lemma tiltCovariance_nonpos_of_pairMass {F : Type u_8} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F)
    (hneg : tiltPairMass μ h i j false false * tiltPairMass μ h i j true true ≤
      tiltPairMass μ h i j true false * tiltPairMass μ h i j false true) :
    tiltCovariance μ h i j ≤ 0 := by
  rw [tiltCovariance_pairMass]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hneg) (sq_nonneg _)

def pairSlice {F : Type u_9} (i j : F) (z w : ℂ) : F → ℂ := by
  classical
  exact fun k => if k = i then z else if k = j then w else 1

lemma prod_pairSlice {F : Type u_10} [Fintype F] (x : F → Bool)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∏ k : F, if x k = true then pairSlice i j z w k else 1) =
      (if x i = true then z else 1) * (if x j = true then w else 1) := by
  classical
  rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp [pairSlice, hij.symm]
  · intro k hk hki
    simp [pairSlice, hki.1, hki.2]

open scoped Classical in
lemma tiltPairMass_generating {F : Type u_11} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (i j : F) (hij : i ≠ j) (z w : ℂ) :
    (∑ x : F → Bool,
      ((Real.exp (∑ k : F, h k * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal : ℝ) : ℂ) *
      ∏ k : F, if x k = true then pairSlice i j z w k else 1) =
      (tiltPairMass μ h i j false false : ℂ) +
      (tiltPairMass μ h i j true false : ℂ) * z +
      (tiltPairMass μ h i j false true : ℂ) * w +
      (tiltPairMass μ h i j true true : ℂ) * z * w := by
  classical
  simp only [tiltPairMass, Complex.ofReal_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [prod_pairSlice x i j hij]
  cases hi : x i <;> cases hj : x j <;> simp [mul_assoc]

end Problem336AdditiveD139

end

end OAI
