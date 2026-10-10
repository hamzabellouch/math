import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Geometry.Determinant

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped MatrixOrder

lemma abs_det_le_prod_mul_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ K i * Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ (∏ i, K i) * Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ ∏ i, K i := by
    apply (abs_det_le_prod_row_norm _).trans
    apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    intro i _
    apply row_norm_le_of_dot_bound_const _ (hK i)
    intro v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ (∏ i, K i)*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = (∏ i, K i) * Real.sqrt P.det := by rw [hQdet]

end CAT0Fillings

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_jacobian_bound_quadratic
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0) (hπ : ∀ i, LipschitzWith (K i) (π i)) :
    ∀ᵐ z ∂volume.restrict C.domain,
      |C.jacobian π z| ≤ (∏ i, (K i : ℝ)) *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hrows : ∀ᵐ z ∂volume.restrict C.domain, ∀ i v,
      |fderivWithin ℝ (C.scalar (π i)) C.domain z v| ≤ K i * p z v := by
    rw [eventually_all]
    intro i
    exact MetricDifferentiation.ae_scalarOn_derivative_bound volume C.borel hL
      (hp.mono fun z hz => hz.1) (hπ i)
  filter_upwards [hp,hrows] with z hz hrow
  apply abs_det_le_prod_mul_sqrt_det_of_posDef _ _
    (polarizationMatrix_posDef b (p z) hz.2.2 hz.2.1) _ (fun i => (K i).coe_nonneg)
  intro i v
  let w : Euc k := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by ext j; simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p z) b).mulVec v = (p z w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p z) hz.2.2 hz.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p z) w)]
  convert hrow i w using 1
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = w := by
    convert b.sum_repr w using 1
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul,smul_eq_mul,dotProduct,mul_comm]

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

end

end OAI
