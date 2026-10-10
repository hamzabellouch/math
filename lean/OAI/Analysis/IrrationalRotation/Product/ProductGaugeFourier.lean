import OAI.Analysis.IrrationalRotation.Rotation.GaugeFourierDiagonal
import OAI.Analysis.IrrationalRotation.Product.ProductFieldDiagonals

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

variable {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
  {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}

def IsCovariantFieldRepresentation.matrixDiagonal
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure *
    multiplier θ (fieldCoefficient F r) B h.1
      (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r)

theorem IsCovariantFieldRepresentation.matrixDiagonal_mem_factor
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    h.matrixDiagonal r ∈ factor θ := h.diagonalOperator_mem_factor r

private theorem single_eq_smul_basis (j : ℤ) (c : ℂ) :
    (lp.single 2 j c : Fiber) = c • (default : HilbertBasis ℤ ℂ Fiber) j := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) j =
      (lp.single 2 j (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) j).symm
  rw [hb]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ℤ => ℂ) 2 j c (1 : ℂ))

private theorem inner_basis_coordinate (j : ℤ) (v : Fiber) :
    inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) j) v = v j :=
  ((default : HilbertBasis ℤ ℂ Fiber).repr_apply_apply v j).symm

theorem IsCovariantFieldRepresentation.coordinate_matrixDiagonal_inclusion
    (h : IsCovariantFieldRepresentation θ A F B) (r k j : ℤ)
    (v : Lp ℂ 2 baseMeasure) :
    DiagonalGauge.coordinate baseMeasure k
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)) =
      if k - j = r then DiagonalGauge.coordinate baseMeasure k
        (A (DiagonalGauge.inclusion baseMeasure j v)) else 0 := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  have hb0 (n : ℤ) : b n = (lp.single 2 n (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single b n).symm
  have hdiag := h.diagonalOperator_ae r (DiagonalGauge.inclusion baseMeasure j v)
  change h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v) =ᵐ[baseMeasure] _ at hdiag
  by_cases hkj : k - j = r
  · rw [ite_eq_left hkj]
    have hk : k = j + r := by omega
    subst k
    apply Lp.ext
    filter_upwards [DiagonalGauge.coordinate_ae baseMeasure (j+r)
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)),
      hdiag, DiagonalGauge.inclusion_ae baseMeasure j v,
      h.diagonalOperator_basis r j,
      DiagonalGauge.coordinate_ae baseMeasure (j+r)
        (A (DiagonalGauge.inclusion baseMeasure j v)),
      h.2.2.2.1 (DiagonalGauge.inclusion baseMeasure j v)] with x hc hd hi hb hcA hA
    rw [hc, hd, hi, single_eq_smul_basis, map_smul, map_smul, hb,
      hcA, hA, hi, single_eq_smul_basis, map_smul]
    change v x * (inner ℂ (b (j+r)) (F x (b j)) * b (j+r) (j+r)) =
      v x * (F x (b j)) (j+r)
    rw [inner_basis_coordinate]
    have hbb : b (j+r) (j+r) = 1 := by
      rw [hb0]
      simp
    rw [hbb, mul_one]
  · rw [ite_eq_right hkj]
    apply Lp.ext
    filter_upwards [DiagonalGauge.coordinate_ae baseMeasure k
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)),
      hdiag, DiagonalGauge.inclusion_ae baseMeasure j v,
      h.diagonalOperator_basis r j,
      Lp.coeFn_zero ℂ 2 baseMeasure] with x hc hd hi hb hz
    rw [hc, hd, hi, single_eq_smul_basis, map_smul, map_smul, hb, hz]
    change v x * (inner ℂ (b (j+r)) (F x (b j)) * b (j+r) k) = 0
    have hbb : b (j+r) k = 0 := by
      rw [hb0]
      have hk : j+r ≠ k := by omega
      simp [lp.single_apply, hk]
    rw [hbb, mul_zero, mul_zero]

theorem IsCovariantFieldRepresentation.fourierOperator_eq_matrixDiagonal
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    DiagonalGauge.fourierOperator baseMeasure A r = h.matrixDiagonal r := by
  apply DiagonalGauge.operator_ext_entries baseMeasure
  intro k j v
  rw [DiagonalGauge.coordinate_fourierOperator_inclusion,
    h.coordinate_matrixDiagonal_inclusion]

theorem IsCovariantFieldRepresentation.fourierOperator_mem_factor
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    DiagonalGauge.fourierOperator baseMeasure A r ∈ factor θ := by
  rw [h.fourierOperator_eq_matrixDiagonal]
  exact h.matrixDiagonal_mem_factor r

theorem IsCovariantFieldRepresentation.matrixDiagonal_neg_apply_integral
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (v : Hilbert) :
    h.matrixDiagonal (-r) v = ∫ t : DiagonalGauge.Circle,
      fourier r t • DiagonalGauge.conjugate baseMeasure A t v
        ∂AddCircle.haarAddCircle := by
  rw [← h.fourierOperator_eq_matrixDiagonal, DiagonalGauge.fourierOperator_apply]
  simp only [neg_neg]

theorem IsCovariantFieldRepresentation.norm_matrixDiagonal_le
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    ‖h.matrixDiagonal r‖ ≤ ‖A‖ := by
  rw [← h.fourierOperator_eq_matrixDiagonal]
  exact DiagonalGauge.norm_fourierOperator_le baseMeasure A r

end Invariant233.ProductModel

end

end OAI
