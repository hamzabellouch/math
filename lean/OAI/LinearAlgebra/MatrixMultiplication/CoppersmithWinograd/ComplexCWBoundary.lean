import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCoppersmithWinograd

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace CWBoundary

open Polynomial

def deleted : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x = 1 ∧ y = 0 ∧ z = 1 then 1 else 0

def tensor : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x = 1 ∧ y = 0 ∧ z = 1 then 0
    else CoppersmithWinograd.tensor x y z

@[simp] theorem tensor_deleted : tensor 1 0 1 = 0 := by simp [tensor]

theorem tensor_preserves (x y z : Fin 3) (h : ¬ (x = 1 ∧ y = 0 ∧ z = 1)) :
    tensor x y z = CoppersmithWinograd.tensor x y z := by simp [tensor, h]

theorem deleted_rankAtMost : Tensor.RankAtMost deleted 1 := by
  have heq : deleted = Tensor.rankOne
      (fun x : Fin 3 => if x = 1 then (1 : ℂ) else 0)
      (fun y : Fin 3 => if y = 0 then (1 : ℂ) else 0)
      (fun z : Fin 3 => if z = 1 then (1 : ℂ) else 0) := by
    funext x y z
    by_cases hx : x = 1 <;> by_cases hy : y = 0 <;> by_cases hz : z = 1 <;>
      simp [deleted, Tensor.rankOne, hx, hy, hz]
  rw [heq]
  exact Tensor.rankOne_rankAtMost _ _ _

section LocalMaps

variable {K : Type*} [CommSemiring K]

def diagonalMap (w : Fin 3 → K) : Fin 3 → Fin 3 → K :=
  fun output input => if input = output then w output else 0

def outerWeight (t : K) (x : Fin 3) : K := if x = 1 then t else 1

def middleWeight (t : K) (y : Fin 3) : K := if y = 1 then 1 else t

def outerMap (t : K) : Fin 3 → Fin 3 → K := diagonalMap (outerWeight t)

def middleMap (t : K) : Fin 3 → Fin 3 → K := diagonalMap (middleWeight t)

theorem restrict_diagonal_apply (a b c : Fin 3 → K)
    (T : Tensor K (Fin 3) (Fin 3) (Fin 3)) (x y z : Fin 3) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T x y z =
      a x * b y * c z * T x y z := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

theorem weight_on_support (t : K) (x y z : Fin 3)
    (hs : x.val + y.val + z.val = 2) :
    outerWeight t x * middleWeight t y * outerWeight t z =
      if x = 1 ∧ y = 0 ∧ z = 1 then t ^ 3 else t := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num at hs <;> norm_num [outerWeight, middleWeight]
  all_goals ring

theorem scale_lifted_tensor (f : ℂ →+* K) (t : K) :
    Tensor.restrict (outerMap t) (middleMap t) (outerMap t)
      (fun x y z => f (CoppersmithWinograd.tensor x y z)) =
      fun x y z => t * f (tensor x y z) + t ^ 3 * f (deleted x y z) := by
  funext x y z
  rw [outerMap, middleMap, restrict_diagonal_apply]
  by_cases hs : x.val + y.val + z.val = 2
  · rw [weight_on_support t x y z hs]
    by_cases hd : x = 1 ∧ y = 0 ∧ z = 1 <;>
      simp [tensor, deleted, CoppersmithWinograd.tensor, hs, hd]
  · by_cases hd : x = 1 ∧ y = 0 ∧ z = 1
    · rcases hd with ⟨rfl, rfl, rfl⟩
      norm_num at hs
    · simp [tensor, deleted, CoppersmithWinograd.tensor, hs, hd]

end LocalMaps

theorem scaling_identity (t : ℂ) :
    Tensor.restrict (outerMap t) (middleMap t) (outerMap t)
      CoppersmithWinograd.tensor =
      fun x y z => t * tensor x y z + t ^ 3 * deleted x y z := by
  simpa using scale_lifted_tensor (RingHom.id ℂ) t

def scalingPolynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  Tensor.restrict (outerMap X) (middleMap X) (outerMap X)
    (fun x y z => C (CoppersmithWinograd.tensor x y z))

theorem scalingPolynomial_apply (x y z : Fin 3) :
    scalingPolynomial x y z = X * C (tensor x y z) + X ^ 3 * C (deleted x y z) := by
  exact congrFun (congrFun (congrFun (scale_lifted_tensor C X) x) y) z

theorem scalingPolynomial_coeff (x y z : Fin 3) (k : ℕ) :
    (scalingPolynomial x y z).coeff k =
      (if k = 1 then tensor x y z else 0) +
        (if k = 3 then deleted x y z else 0) := by
  rw [scalingPolynomial_apply, Polynomial.coeff_add,
    mul_comm X (C (tensor x y z)), mul_comm (X ^ 3) (C (deleted x y z)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem scalingPolynomial_leading (x y z : Fin 3) :
    (scalingPolynomial x y z).coeff 1 = tensor x y z := by
  simp [scalingPolynomial_coeff]

theorem scalingPolynomial_degree (x y z : Fin 3) :
    (scalingPolynomial x y z).degree ≤ 3 := by
  rw [scalingPolynomial_apply,
    mul_comm X (C (tensor x y z)), mul_comm (X ^ 3) (C (deleted x y z))]
  apply Polynomial.degree_add_le_of_degree_le
  · exact (Polynomial.degree_C_mul_X_le (tensor x y z)).trans (by norm_num)
  · exact Polynomial.degree_C_mul_X_pow_le 3 (deleted x y z)

def normalizedCurve (t : ℂ) : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => tensor x y z + t ^ 2 * deleted x y z

theorem normalizedCurve_restriction (t : ℂ) (ht : t ≠ 0) :
    normalizedCurve t = Tensor.restrict
      (diagonalMap (fun x => t⁻¹ * outerWeight t x))
      (middleMap t) (outerMap t) CoppersmithWinograd.tensor := by
  funext x y z
  rw [middleMap, outerMap, restrict_diagonal_apply]
  have h := congrFun (congrFun (congrFun (scaling_identity t) x) y) z
  rw [outerMap, middleMap, restrict_diagonal_apply] at h
  calc
    normalizedCurve t x y z =
        (t⁻¹ * t) * tensor x y z + (t⁻¹ * t) * t ^ 2 * deleted x y z := by
      simp [normalizedCurve, inv_mul_cancel₀ ht]
    _ = t⁻¹ * (t * tensor x y z + t ^ 3 * deleted x y z) := by ring
    _ = t⁻¹ * (outerWeight t x * middleWeight t y * outerWeight t z *
        CoppersmithWinograd.tensor x y z) := by rw [h]
    _ = _ := by ring

theorem degeneration : Tensor.DegeneratesTo CoppersmithWinograd.tensor tensor := by
  have hf : Continuous normalizedCurve := by
    unfold normalizedCurve
    fun_prop
  have hclosed : IsClosed {t : ℂ | normalizedCurve t ∈
      closure (Tensor.restrictionOrbit CoppersmithWinograd.tensor)} :=
    isClosed_closure.preimage hf
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ {t : ℂ | normalizedCurve t ∈
      closure (Tensor.restrictionOrbit CoppersmithWinograd.tensor)} := by
    intro t ht
    apply subset_closure
    exact ⟨diagonalMap (fun x => t⁻¹ * outerWeight t x), middleMap t, outerMap t,
      normalizedCurve_restriction t (by simpa using ht)⟩
  have hz := closure_minimal hsubset hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  have heq : normalizedCurve 0 = tensor := by
    funext x y z
    simp [normalizedCurve]
  change normalizedCurve 0 ∈
    closure (Tensor.restrictionOrbit CoppersmithWinograd.tensor) at hz
  rw [heq] at hz
  exact hz

def weight (x y z : Fin 3) : ℕ :=
  (if x = 1 then 1 else 0) + (if y = 1 then 0 else 1) +
    (if z = 1 then 1 else 0)

def polynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  Tensor.restrict (outerMap X) (middleMap X) (outerMap X)
    CoppersmithWinograd.polynomial

theorem polynomial_rankAtMost : Tensor.RankAtMost polynomial 3 :=
  CoppersmithWinograd.rank_bound.restrict (outerMap X) (middleMap X) (outerMap X)

theorem polynomial_apply (x y z : Fin 3) :
    polynomial x y z =
      if x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
          x.val + y.val + z.val = 6 then
        X ^ (x.val + y.val + z.val + weight x y z) else 0 := by
  unfold polynomial outerMap middleMap
  rw [restrict_diagonal_apply, CoppersmithWinograd.polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6
  · simp only [ite_eq_left hs]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> by_cases hz : z = 1 <;>
      simp [outerWeight, middleWeight, weight, hx, hy, hz, pow_add] <;> ring
  · simp [hs]

theorem weighted_degree (x y z : Fin 3)
    (hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6) :
    (x.val + y.val + z.val + weight x y z = 3 ↔
      x.val + y.val + z.val = 2 ∧ ¬ (x = 1 ∧ y = 0 ∧ z = 1)) ∧
    3 ≤ x.val + y.val + z.val + weight x y z ∧
    x.val + y.val + z.val + weight x y z ≤ 7 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num at hs <;> norm_num [weight]

theorem polynomial_leading (x y z : Fin 3) :
    (polynomial x y z).coeff 3 = tensor x y z := by
  rw [polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6
  · simp only [ite_eq_left hs, Polynomial.coeff_X_pow]
    have hd : (3 = x.val + y.val + z.val + weight x y z) ↔
        (x.val + y.val + z.val = 2 ∧ ¬ (x = 1 ∧ y = 0 ∧ z = 1)) :=
      eq_comm.trans (weighted_degree x y z hs).1
    simp only [hd]
    by_cases hb : x = 1 ∧ y = 0 ∧ z = 1 <;>
      by_cases htwo : x.val + y.val + z.val = 2 <;>
      simp [tensor, CoppersmithWinograd.tensor, hb, htwo]
  · have htwo : x.val + y.val + z.val ≠ 2 := fun h => hs (Or.inl h)
    rw [ite_eq_right hs]
    simp [tensor, CoppersmithWinograd.tensor, htwo]

theorem polynomial_vanishes (x y z : Fin 3) (k : ℕ) (hk : k < 3) :
    (polynomial x y z).coeff k = 0 := by
  rw [polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6
  · have hd := (weighted_degree x y z hs).2.1
    have hne : k ≠ x.val + y.val + z.val + weight x y z := by omega
    simp [hs, Polynomial.coeff_X_pow, hne]
  · simp [hs]

theorem polynomial_degree (x y z : Fin 3) : (polynomial x y z).degree ≤ 7 := by
  rw [polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6
  · rw [ite_eq_left hs]
    apply Polynomial.degree_le_of_natDegree_le
    rw [Polynomial.natDegree_X_pow]
    exact (weighted_degree x y z hs).2.2
  · simp [hs]

def approximation : Tensor.PolynomialApproximation tensor 3 3 7 where
  polynomial := polynomial
  rank_bound := polynomial_rankAtMost
  vanishes := polynomial_vanishes
  leading := polynomial_leading
  degree_bound := polynomial_degree

theorem borderRankAtMost : Tensor.BorderRankAtMost tensor 3 :=
  approximation.borderRankAtMost

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power tensor n) ((7 * n + 1) * 3 ^ n) :=
  approximation.rank_power n

end CWBoundary
end MatrixMultiplication.Foundation

end

end OAI
