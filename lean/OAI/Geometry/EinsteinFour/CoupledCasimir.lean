import OAI.Geometry.EinsteinFour.CoupledOperator
import OAI.Geometry.EinsteinFour.BianchiSlices

namespace OAI

/-! The plus spectral polynomial on the actual highest-Hessian space. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def rawSlice (X : Hessian) (i : Fin 4) : RawGradient := fun b c =>
  WithLp.toLp 2 (fun j => X i j b c)

def outerAction (s : Fin 3) (X : Hessian) : Hessian := fun i j b c =>
  quaternion s (WithLp.toLp 2 (fun k => X k j b c)) i

def innerAction (s : Fin 3) (X : Hessian) : Hessian := fun i j b c =>
  matrixAction s (X i j) b c + ∑ k, quaternionMatrix s j k * X i k b c

theorem outerAction_add (s : Fin 3) (X Y : Hessian) :
    outerAction s (X + Y) = outerAction s X + outerAction s Y := by
  funext i j b c
  fin_cases s <;> fin_cases i <;> simp [outerAction, quaternion]
  all_goals ring

theorem innerAction_add (s : Fin 3) (X Y : Hessian) :
    innerAction s (X + Y) = innerAction s X + innerAction s Y := by
  funext i j b c
  simp [innerAction, matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

theorem outerAction_square (s : Fin 3) (X : Hessian) :
    outerAction s (outerAction s X) = -X := by
  funext i j b c
  have h := congrArg (fun v : Vec => v i)
    (quaternion_square s (WithLp.toLp 2 (fun k => X k j b c)))
  exact h

theorem innerAction_outerAction (s r : Fin 3) (X : Hessian) :
    innerAction s (outerAction r X) = outerAction r (innerAction s X) := by
  funext i j b c
  fin_cases r <;> fin_cases i <;>
    simp [innerAction, outerAction, quaternion, matrixAction,
      Fin.sum_univ_three, Fin.sum_univ_four]
  all_goals ring

theorem totalPlus_inner_outer (s : Fin 3) (X : Hessian) :
    totalPlus s X = innerAction s X + outerAction s X := by
  funext i j b c
  change totalPlus s X i j b c = innerAction s X i j b c + outerAction s X i j b c
  rw [show outerAction s X i j b c =
    ∑ k, quaternionMatrix s i k * X k j b c from
      (quaternionMatrix_apply s (WithLp.toLp 2 (fun k => X k j b c)) i).symm]
  simp only [totalPlus, innerAction]
  ring

theorem coupledOperator_outer_inner (X : Hessian) :
    coupledOperator X = ∑ s : Fin 3, outerAction s (innerAction s X) := by
  funext i j b c
  simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.add_apply]
  rw [coupledOperator_apply]
  simp only [Fin.sum_univ_three]
  have h (s : Fin 3) := quaternionMatrix_apply s
    (WithLp.toLp 2 (fun k => innerAction s X k j b c)) i
  simp only [outerAction]
  rw [← h 0, ← h 1, ← h 2]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k _
      simp only [innerAction]
      ring
    · apply Finset.sum_congr rfl
      intro k _
      simp only [innerAction]
      ring
  · apply Finset.sum_congr rfl
    intro k _
    simp only [innerAction]
    ring

/-- The total Casimir separates into the two actual tensor factors. -/
theorem totalPlus_casimir_split (X : Hessian) :
    (∑ s : Fin 3, totalPlus s (totalPlus s X)) =
      (-3 : ℝ) • X + (∑ s : Fin 3, innerAction s (innerAction s X)) +
        (2 : ℝ) • coupledOperator X := by
  have h (s : Fin 3) : totalPlus s (totalPlus s X) =
      innerAction s (innerAction s X) +
        (2 : ℝ) • outerAction s (innerAction s X) - X := by
    rw [totalPlus_inner_outer, totalPlus_inner_outer, innerAction_add,
      outerAction_add, innerAction_outerAction, outerAction_square]
    module
  simp_rw [h]
  rw [coupledOperator_outer_inner]
  simp only [Fin.sum_univ_three]
  module

theorem innerAction_rawSlice (s : Fin 3) (X : Hessian) (i : Fin 4) :
    rawSlice (innerAction s X) i = rawGradientGenerator s (rawSlice X i) := by
  funext b c
  ext j
  have h := quaternionMatrix_apply s (rawSlice X i b c) j
  simp only [rawSlice, Fin.sum_univ_four] at h
  simp [rawSlice, innerAction, rawGradientGenerator, rawMatrixRotation,
    matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← h]
  ring

/-- The inner Casimir acts on the actual Bianchi slices. -/
theorem innerAction_casimir_of_condition (X : Hessian) (hX : condition X) :
    (∑ s : Fin 3, innerAction s (innerAction s X)) = (-35 : ℝ) • X := by
  funext i j b c
  simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.add_apply]
  obtain ⟨hz, hb⟩ := innerSlice_of_condition X hX i
  have hr : rawSlice X i = (innerSlice X i).matrix := by
    funext a b
    exact (innerSlice_matrix X i (fun j => (hX.2.1 i j).1) a b).symm
  have hh := rawGradientGenerator_casimir (innerSlice X i) hz hb b c
  have h := congrArg (fun v : Vec => v j) hh
  have hs (s : Fin 3) : innerAction s (innerAction s X) i j b c =
      rawGradientGenerator s (rawGradientGenerator s (innerSlice X i).matrix) b c j := by
    change rawSlice (innerAction s (innerAction s X)) i b c j = _
    rw [innerAction_rawSlice, innerAction_rawSlice, hr]
  simp only [Fin.sum_univ_three] at h ⊢
  simp only [hs]
  simpa [← hr, rawSlice] using h

/-- The spectral value is derived from the three already computed Casimirs. -/
theorem coupledOperator_of_condition (X : Hessian) (hX : condition X) :
    coupledOperator X = (-5 : ℝ) • X := by
  have h48 : (∑ s : Fin 3, totalPlus s (totalPlus s X)) = (-48 : ℝ) • X := by
    obtain ⟨c, rfl⟩ := exists_highest X hX
    simpa only [Fin.sum_univ_three] using totalPlus_casimir c
  rw [totalPlus_casimir_split, innerAction_casimir_of_condition X hX] at h48
  funext i j b c
  have h := congrArg (fun Y : Hessian => Y i j b c) h48
  change -3 * X i j b c + -35 * X i j b c +
    2 * coupledOperator X i j b c = -48 * X i j b c at h
  change coupledOperator X i j b c = -5 * X i j b c
  linarith

/-- The explicit polynomial fixes the concrete highest-Hessian subspace. -/
theorem plusPolynomial_of_condition (X : Hessian) (hX : condition X) :
    plusPolynomial X = X := by
  rw [plusPolynomial, coupledOperator_of_condition X hX]
  module


/-- The real polynomial preserves pairings with every highest tensor. -/
theorem plusPolynomial_pairing (L Y : Hessian) (hY : condition Y) :
    hessianPairing (plusPolynomial L) Y = hessianPairing L Y := by
  have hK := coupledOperator_selfadjoint L Y
  rw [coupledOperator_of_condition Y hY] at hK
  have hR : hessianPairing L ((-5 : ℝ) • Y) = -5 * hessianPairing L Y := by
    rw [hessianPairing_comm, hessianPairing_smul_left, hessianPairing_comm Y L]
  rw [hR] at hK
  have hS : hessianPairing ((7 : ℝ) • L - coupledOperator L) Y =
      7 * hessianPairing L Y - hessianPairing (coupledOperator L) Y := by
    change (∑ a, ∑ b, ∑ i, ∑ j,
      (7 * L i j a b - coupledOperator L i j a b) * Y i j a b) = _
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hessianPairing]
  rw [plusPolynomial, hessianPairing_smul_left, hS, hK]
  ring

/-- The constructed highest projection factors through the real polynomial. -/
theorem highestProjection_plusPolynomial (L : Hessian) :
    highestProjection (plusPolynomial L) = highestProjection L := by
  let A := highestProjection (plusPolynomial L)
  let B := highestProjection L
  have hA : condition A := highestProjection_condition _
  have hB : condition B := highestProjection_condition _
  have hAA : hessianPairing A A = hessianPairing B A := by
    rw [show A = highestProjection (plusPolynomial L) from rfl,
      highestProjection_pairing_right _ A hA, plusPolynomial_pairing L A hA,
      show B = highestProjection L from rfl, highestProjection_pairing_right L A hA]
  have hAB : hessianPairing A B = hessianPairing B B := by
    rw [show A = highestProjection (plusPolynomial L) from rfl,
      highestProjection_pairing_right _ B hB, plusPolynomial_pairing L B hB,
      show B = highestProjection L from rfl, highestProjection_pairing_right L B hB]
  have hn : hessianNormSq (A - B) = 0 := by
    rw [hessianNormSq_sub, ← hessianPairing_self A, ← hessianPairing_self B]
    rw [hAA, hessianPairing_comm B A, hAB]
    ring
  have hv : ‖hessianVector (A - B)‖ = 0 := by
    have hh : ‖hessianVector (A - B)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, hessianVector_inner, hessianPairing_self]
      exact hn
    nlinarith [norm_nonneg (hessianVector (A - B))]
  have hz : A - B = 0 := by
    apply hessianVector_injective
    rw [norm_eq_zero.mp hv]
    ext p
    rfl
  exact sub_eq_zero.mp hz

end
end PositiveEinsteinFour.HighestHessian

end OAI
