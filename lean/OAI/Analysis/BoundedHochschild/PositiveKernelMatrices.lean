import OAI.Analysis.WeakInfiniteness.MatrixRepresentation
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

namespace OAI

/-! Positive finite Gram matrices and the coefficient inequality needed for
the Hilbert-space construction of completely positive maps. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

/-- The Gram matrix of a finite family in the algebra. -/
def algebraGram (a : I → M) : CStarMatrix I I M := fun i j => star (a i) * a j

lemma algebraGram_nonneg (a : I → M) : 0 ≤ algebraGram a := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    have hz : algebraGram a = 0 := by ext i; exact isEmptyElim i
    rw [hz]
  | inr h =>
    let i₀ : I := Classical.choice h
    let R : CStarMatrix I I M := fun i j => if i = i₀ then a j else 0
    have heq : star R * R = algebraGram a := by
      ext i j
      change (∑ k, star (if k = i₀ then a i else 0) *
        (if k = i₀ then a j else 0)) = star (a i) * a j
      simp
    rw [← heq]
    exact star_mul_self_nonneg R

/-- Inserting any positive algebra element still gives a positive matrix. -/
lemma weighted_algebraGram_nonneg (a : I → M) (q : M) (hq : 0 ≤ q) :
    0 ≤ CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
  have hs : star (CFC.sqrt q) * CFC.sqrt q = q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have heq : algebraGram (fun i => CFC.sqrt q * a i) =
      CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
    ext i j
    change star (CFC.sqrt q * a i) * (CFC.sqrt q * a j) = _
    rw [star_mul]
    calc
      _ = star (a i) * (star (CFC.sqrt q) * CFC.sqrt q) * a j := by
        simp only [mul_assoc]
      _ = _ := by rw [hs]; rfl
  rw [← heq]
  exact algebraGram_nonneg (fun i : I => CFC.sqrt q * a i)

/-- Left multiplication is bounded in every one of these positive kernels. -/
lemma algebraGram_left_le (a : I → M) (b : M) :
    algebraGram (fun i => b * a i) ≤ ‖b‖ ^ 2 • algebraGram a := by
  have hb : star b * b ≤ ‖b‖ ^ 2 • (1 : M) := by
    simpa only [star_one, one_mul, mul_one, CStarRing.norm_star_mul_self, pow_two]
      using CStarAlgebra.star_left_conjugate_le_norm_smul (1 : M) (star b * b)
  have hq := weighted_algebraGram_nonneg a (‖b‖ ^ 2 • (1 : M) - star b * b)
    (sub_nonneg.mpr hb)
  have heq : CStarMatrix.ofMatrix (fun i j => star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j) = ‖b‖ ^ 2 • algebraGram a - algebraGram (fun i => b * a i) := by
    ext i j
    change star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j =
      ‖b‖ ^ 2 • (star (a i) * a j) - star (b * a i) * (b * a j)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, star_mul, mul_assoc]
  rw [heq] at hq
  exact sub_nonneg.mp hq

/-- Positivity of operator matrices implies positivity of their finite
quadratic forms, with arbitrary Hilbert-space vectors. -/
lemma operatorMatrix_quadratic_nonneg
    (A : CStarMatrix I I (H →L[ℂ] H)) (hA : 0 ≤ A) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j)) := by
  have h := map_nonneg (WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)) hA
  have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp h).inner_nonneg_right
    (WithLp.toLp 2 ξ)
  change 0 ≤ inner ℂ (WithLp.toLp 2 ξ)
    (WeakPureInfiniteness.matrixOperator A (WithLp.toLp 2 ξ)) at hi
  simpa only [PiLp.inner_apply, WeakPureInfiniteness.matrixOperator_apply,
    PiLp.toLp_apply, inner_sum] using hi

/-- A completely positive map produces positive finite coefficient kernels. -/
lemma completelyPositive_kernel_nonneg
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j)) := by
  exact operatorMatrix_quadratic_nonneg _
    (φ.map_cstarMatrix_nonneg (algebraGram a) (algebraGram_nonneg a)) ξ

end BoundedHochschild.KadisonRingrose

end

end OAI
