import OAI.Geometry.EinsteinFour.GradientOperator
import OAI.Geometry.EinsteinFour.TensorPairing

namespace OAI

/-! The real-vector norm calculation behind the plus projection cost. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The real quaternion frame is orthogonal, with common norm `|a|`.
This includes the scalar direction and avoids any complex factorization. -/
theorem quaternion_combination_norm_sq (a : Vec) (r : ℝ) (c : Fin 3 → ℝ) :
    (∑ i : Fin 4, (r * a i + ∑ s : Fin 3, c s * quaternion s a i) ^ 2) =
      (r ^ 2 + ∑ s : Fin 3, c s ^ 2) * ‖a‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, quaternion, Fin.sum_univ_succ]
  ring

/-- The coupled action on a real rank-one weight tensor. -/
def weightCoupling (a : Vec) (Z : Tensor) : Hessian := fun i j b c =>
  ∑ s : Fin 3, quaternion s a i * gradientGenerator s Z b c j

/-- The twice-coupled action, retaining the ordered generator products. -/
def weightDoubleCoupling (a : Vec) (Z : Tensor) : Hessian := fun i j b c =>
  ∑ s : Fin 3, ∑ r : Fin 3, quaternion s (quaternion r a) i *
    rawGradientGenerator s (rawGradientGenerator r Z.matrix) b c j

/-- The coupled polynomial follows from the actual generator commutators and
Casimir, rather than a tensor-representation decomposition. -/
theorem weightCoupling_polynomial (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (i j : Fin 4) (b c : Fin 3) :
    weightDoubleCoupling a Z i j b c =
      35 * a i * Z.matrix b c j + 2 * weightCoupling a Z i j b c := by
  have hC := congrArg (fun v : Vec => v j)
    (rawGradientGenerator_casimir Z hz hb b c)
  have h01 := congrArg (fun V : RawGradient => V b c j)
    (rawGradientGenerator_commutator 0 Z.matrix)
  have h12 := congrArg (fun V : RawGradient => V b c j)
    (rawGradientGenerator_commutator 1 Z.matrix)
  have h20 := congrArg (fun V : RawGradient => V b c j)
    (rawGradientGenerator_commutator 2 Z.matrix)
  simp [next, previous, Fin.sum_univ_three] at hC h01 h12 h20
  fin_cases i <;>
    simp [weightDoubleCoupling, weightCoupling, quaternion, Fin.sum_univ_three]
  · linear_combination -(a 0) * hC - (a 3) * h01 - (a 1) * h12 - (a 2) * h20
  · linear_combination -(a 1) * hC - (a 2) * h01 + (a 0) * h12 + (a 3) * h20
  · linear_combination -(a 2) * hC + (a 1) * h01 - (a 3) * h12 + (a 0) * h20
  · linear_combination -(a 3) * hC + (a 0) * h01 + (a 2) * h12 - (a 1) * h20

/-- The explicit polynomial `(7-K)(a ⊗ Z)/12`, where
`K = Σ I_outer,s ⊗ (I_inner,s + Σ_s)`. -/
def weightPlusPart (a : Vec) (Z : Tensor) : Hessian := fun i j b c =>
  (7 * a i * Z.matrix b c j - weightCoupling a Z i j b c) / 12

private theorem weightPlusPart_outer_norm (a : Vec) (Z : Tensor)
    (b c : Fin 3) (j : Fin 4) :
    (∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2) =
      (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
        ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
  have h := quaternion_combination_norm_sq a (7 * Z.matrix b c j)
    (fun s => -gradientGenerator s Z b c j)
  have hentry (i : Fin 4) :
      7 * a i * Z.matrix b c j -
          ∑ s : Fin 3, quaternion s a i * gradientGenerator s Z b c j =
        (7 * Z.matrix b c j) * a i +
          ∑ s : Fin 3, (-gradientGenerator s Z b c j) * quaternion s a i := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [weightPlusPart, weightCoupling, hentry, div_pow, ← Finset.sum_div]
  rw [h]
  simp only [neg_sq, mul_pow]
  ring

/-- The coefficient `7/12` is proved directly for real vectors using the
actual Bianchi Casimir, with no representation or partial-trace premise. -/
theorem weightPlusPart_norm (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianNormSq (weightPlusPart a Z) = (7 / 12) * ‖a‖ ^ 2 * Z.squaredNorm := by
  have hZ : (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) = Z.squaredNorm := by
    simp only [Tensor.squaredNorm, EuclideanSpace.real_norm_sq_eq]
  have hG : (∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3,
      gradientGenerator s Z b c j ^ 2) = 35 * Z.squaredNorm := by
    calc
      _ = ∑ b, ∑ c, ∑ s : Fin 3, ∑ j : Fin 4,
          gradientGenerator s Z b c j ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = _ := by
        simpa only [EuclideanSpace.real_norm_sq_eq] using gradientGenerator_energy Z hz hb
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2 := by
      unfold hessianNormSq
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ j : Fin 4,
        (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
          ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp_rw [weightPlusPart_outer_norm]
    _ = (‖a‖ ^ 2 / 144) *
        (49 * (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) +
          ∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hZ, hG]; ring

end
end PositiveEinsteinFour.Bianchi

end OAI
