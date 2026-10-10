import OAI.NumberTheory.Ostmann.Supply.BilinearCube
import OAI.NumberTheory.Ostmann.Supply.ElementaryPolynomial

namespace OAI

/-! # Exact truncation of the two subset choices -/
namespace Ostmann
open scoped Classical BigOperators

theorem cubeCoefficient_truncation {n : ℕ} (A : BilinearCube n → ℂ) (K : ℕ) :
    rectangularPolynomialSum (cubeCoefficient A) (n + 1) K =
      ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K), A v := by
  let B : BilinearCube n → ℂ := fun v =>
    if cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K then A v else 0
  have hc (j k : ℕ) : cubeCoefficient B j k =
      if j ≤ K ∧ k ≤ K then cubeCoefficient A j k else 0 := by
    unfold cubeCoefficient
    calc
      _ = ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
          (fun v => (cubeDegree v false, cubeDegree v true) = (j, k)),
          if j ≤ K ∧ k ≤ K then A v else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        have he := (Finset.mem_filter.mp hv).2
        have hj : cubeDegree v false = j := congrArg Prod.fst he
        have hk : cubeDegree v true = k := congrArg Prod.snd he
        dsimp only [B]
        simp only [hj, hk]
      _ = _ := by by_cases h : j ≤ K ∧ k ≤ K <;> simp [h]
  have hh := cubeCoefficient_polynomial B 1 1
  simp only [finitePolynomial₂, finitePolynomial, hc, one_pow, one_mul,
    smul_eq_mul] at hh
  simpa only [rectangularPolynomialSum, B, Finset.sum_filter] using hh

noncomputable def subsetPairFactor (b : ℂ) : Bool × Bool → ℂ
  | (false, false) => 1
  | (true, false) => b
  | (false, true) => b
  | (true, true) => b ^ 2

theorem subsetPair_cubeCoefficient {n : ℕ} (b : Fin n → ℂ)
    (j k : ℕ) (hj : j < n + 1) (hk : k < n + 1) :
    cubeCoefficient (fun v => ∏ i, subsetPairFactor (b i) (v i)) j k =
      elementaryCoefficient b j * elementaryCoefficient b k := by
  apply finitePolynomial₂_coefficient_unique (N := n + 1) _ _ _ j k hj hk
  intro u v
  rw [← bilinear_product_expansion, elementaryCoefficient_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [subsetPairFactor]
  ring

theorem elementaryTruncation_square_cube {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    elementaryTruncation b K ^ 2 =
      ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
          ∏ i, subsetPairFactor (b i) (v i) := by
  rw [← cubeCoefficient_truncation, ← elementaryTruncation_square]
  unfold rectangularPolynomialSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j ≤ K ∧ k ≤ K
  · simp only [h]
    exact (subsetPair_cubeCoefficient b j k (Finset.mem_range.mp hj)
      (Finset.mem_range.mp hk)).symm
  · simp only [h, ite_false]

end Ostmann

end OAI
