import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

/-- Squared local Fock coefficient, with `true` denoting differentiation. -/
def mass (derivative : Bool) (z : ℕ) : ℝ :=
  if derivative then z else z + 1

def coefficient (derivative : Bool) (z : ℕ) : ℝ :=
  Real.sqrt (mass derivative z)

lemma mass_nonneg (derivative : Bool) (z : ℕ) : 0 ≤ mass derivative z := by
  cases derivative <;> dsimp [mass]
  all_goals positivity

@[simp] lemma coefficient_sq (derivative : Bool) (z : ℕ) :
    coefficient derivative z ^ 2 = mass derivative z :=
  Real.sq_sqrt (mass_nonneg derivative z)

/-- One layer's four factors in the second trace. -/
def fourCoefficient (derivative : Bool) (a b c d : ℕ) : ℝ :=
  coefficient derivative a * coefficient derivative b *
    coefficient derivative c * coefficient derivative d

/-- The normal pairing has zero occupation shift. -/
lemma normal_fourCoefficient (derivative : Bool) (a b : ℕ) :
    fourCoefficient derivative a a b b = mass derivative a * mass derivative b := by
  calc
    _ = coefficient derivative a ^ 2 * coefficient derivative b ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by rw [coefficient_sq, coefficient_sq]

/-- Differentiating diagonal pairing: the second path receives one occupation. -/
lemma derivative_diagonal_fourCoefficient (a b : ℕ) :
    fourCoefficient true a (b + 1) a (b + 1) = (a : ℝ) * ((b : ℝ) + 1) := by
  calc
    _ = coefficient true a ^ 2 * coefficient true (b + 1) ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by simp [mass]

/-- Multiplying diagonal pairing, expressed without natural subtraction. -/
lemma multiplication_diagonal_fourCoefficient (a b : ℕ) :
    fourCoefficient false a b a b = ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
  calc
    _ = coefficient false a ^ 2 * coefficient false b ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by simp [mass]

lemma multiplication_diagonal_fourCoefficient_pred (a b : ℕ) (hb : 0 < b) :
    fourCoefficient false a (b - 1) a (b - 1) = ((a : ℝ) + 1) * (b : ℝ) := by
  rw [multiplication_diagonal_fourCoefficient]
  have h : (b - 1 : ℕ) + 1 = b := by omega
  have hr := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast at hr
  rw [hr]

/-- The unavailable differentiation contribution vanishes identically. -/
@[simp] lemma derivative_invalid (b : ℕ) :
    (0 : ℝ) * ((b : ℝ) + 1) = 0 := zero_mul _

/-- If the multiplication shift would create a negative source occupation,
its table contribution is zero. -/
@[simp] lemma multiplication_invalid (a : ℕ) :
    ((a : ℝ) + 1) * (0 : ℝ) = 0 := mul_zero _

/-- Move the four path products into a product of local four-factor entries. -/
lemma four_products_eq_product {ι : Type*} (s : Finset ι)
    (derivative : ι → Bool) (a b c d : ι → ℕ) :
    (∏ i ∈ s, coefficient (derivative i) (a i)) *
      (∏ i ∈ s, coefficient (derivative i) (b i)) *
      (∏ i ∈ s, coefficient (derivative i) (c i)) *
      (∏ i ∈ s, coefficient (derivative i) (d i)) =
    ∏ i ∈ s, fourCoefficient (derivative i) (a i) (b i) (c i) (d i) := by
  simp only [fourCoefficient, Finset.prod_mul_distrib]

/-- Version of the normal pairing usable with occupation functions. -/
lemma normal_layer {σ : Type*} (derivative : Bool) (M M' : σ → ℕ) (i j : σ)
    (hi : M' i = M i) (hj : M' j = M j) :
    fourCoefficient derivative (M i) (M' i) (M j) (M' j) =
      mass derivative (M i) * mass derivative (M j) := by
  rw [hi, hj, normal_fourCoefficient]

lemma derivative_diagonal_layer {σ : Type*} (M M' : σ → ℕ) (i j : σ)
    (hj : M' j = M j + 1) :
    fourCoefficient true (M i) (M' j) (M i) (M' j) =
      (M i : ℝ) * ((M j : ℝ) + 1) := by
  rw [hj, derivative_diagonal_fourCoefficient]

lemma multiplication_diagonal_layer {σ : Type*} (M M' : σ → ℕ) (i j : σ)
    (hj : M' j + 1 = M j) :
    fourCoefficient false (M i) (M' j) (M i) (M' j) =
      ((M i : ℝ) + 1) * (M j : ℝ) := by
  rw [multiplication_diagonal_fourCoefficient]
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hj
  push_cast at hr
  rw [hr]

/-- The multiplying diagonal term, extended by zero when its backward shift is invalid. -/
def multiplicationDiagonalTerm (a b : ℕ) : ℝ :=
  if b = 0 then 0 else fourCoefficient false a (b - 1) a (b - 1)

lemma multiplicationDiagonalTerm_eq (a b : ℕ) :
    multiplicationDiagonalTerm a b = ((a : ℝ) + 1) * (b : ℝ) := by
  by_cases hb : b = 0
  · simp [multiplicationDiagonalTerm, hb]
  · simp only [multiplicationDiagonalTerm, hb, ↓reduceIte]
    exact multiplication_diagonal_fourCoefficient_pred a b (Nat.pos_of_ne_zero hb)

lemma square_fallingFactorial (z : ℕ) :
    (z : ℝ)^2 = (z.descFactorial 2 : ℝ) + (z : ℝ) := by
  cases z with
  | zero => norm_num
  | succ z => simp [Nat.descFactorial_succ]; ring

lemma successor_square_fallingFactorial (z : ℕ) :
    ((z : ℝ) + 1)^2 = (z.descFactorial 2 : ℝ) + 3 * (z : ℝ) + 1 := by
  rw [show ((z : ℝ) + 1)^2 = (z : ℝ)^2 + 2 * z + 1 by ring,
    square_fallingFactorial]
  ring

/-- Geometric first/second-moment input, before normalization, for normal pairings. -/
def normalGeometricMass (derivative : Bool) (G : ℝ) (collision : Bool) : ℝ :=
  if derivative then
    if collision then 2 * G^2 + G else G^2
  else
    if collision then 2 * G^2 + 3 * G + 1 else (G + 1)^2

def diagonalGeometricMass (G : ℝ) : ℝ := G * (G + 1)

lemma derivative_normal_weight (G : ℝ) (hG : 0 < G) (collision : Bool) :
    normalGeometricMass true G collision / G^2 =
      1 + (G / (G + 1))⁻¹ * (if collision then 1 else 0) := by
  have h0 : G ≠ 0 := ne_of_gt hG
  have h1 : G + 1 ≠ 0 := ne_of_gt (by linarith)
  cases collision <;> simp [normalGeometricMass, h0]
  all_goals field_simp
  all_goals ring

lemma multiplication_normal_weight (G : ℝ) (hG : 0 ≤ G) (collision : Bool) :
    normalGeometricMass false G collision / (G + 1)^2 =
      1 + (G / (G + 1)) * (if collision then 1 else 0) := by
  have h1 : G + 1 ≠ 0 := ne_of_gt (by linarith)
  cases collision <;> simp [normalGeometricMass, h1]
  all_goals field_simp
  all_goals ring

lemma derivative_diagonal_weight (G : ℝ) (hG : 0 < G) :
    diagonalGeometricMass G / G^2 = (G / (G + 1))⁻¹ := by
  have h0 : G ≠ 0 := ne_of_gt hG
  have h1 : G + 1 ≠ 0 := ne_of_gt (by linarith)
  unfold diagonalGeometricMass
  field_simp

lemma multiplication_diagonal_weight (G : ℝ) (hG : 0 ≤ G) :
    diagonalGeometricMass G / (G + 1)^2 = G / (G + 1) := by
  have h1 : G + 1 ≠ 0 := ne_of_gt (by linarith)
  unfold diagonalGeometricMass
  field_simp

end LocalMoments
end Problem335

end

end OAI
