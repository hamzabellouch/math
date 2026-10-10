import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.ChartMass
import OAI.Geometry.CAT0Fillings.Radial.IntrinsicSlope

namespace OAI

section
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

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma aestronglyMeasurable_radialJacobian
    (P : Euc k → Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, Measurable (fun z => P z i j))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (t : ℝ) :
    AEStronglyMeasurable (C.radialJacobian P o g t) (volume.restrict C.domain) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  obtain ⟨G,hG,heG⟩ := (C.scalar_lipschitzOn hL hg).extend_real
  have hrm := C.measurable_scalar (LipschitzWith.dist_right o)
  have hgm := C.measurable_scalar hg
  let J : Euc k → ℝ := fun z => Real.sqrt (metricSpatialRadialForm (P z)
    (C.scalar g z) (C.scalar (dist o) z) t
    (differentialRow (fderiv ℝ R z)) (differentialRow (fderiv ℝ G z))).det
  have hRd (i : Fin k) : Measurable (fun z => differentialRow (fderiv ℝ R z) i) := by
    simp only [differentialRow]
    fun_prop
  have hGd (i : Fin k) : Measurable (fun z => differentialRow (fderiv ℝ G z) i) := by
    simp only [differentialRow]
    fun_prop
  have hEntry (i j : Fin k) : Measurable (fun z => (metricSpatialRadialForm (P z)
      (C.scalar g z) (C.scalar (dist o) z) t
      (differentialRow (fderiv ℝ R z)) (differentialRow (fderiv ℝ G z))) i j) := by
    change Measurable (fun z =>
      (1-t*C.scalar g z)^2*(P z i j)-
      ((1-t*C.scalar g z)*t*C.scalar (dist o) z)*
        (differentialRow (fderiv ℝ R z) i*differentialRow (fderiv ℝ G z) j+
         differentialRow (fderiv ℝ G z) i*differentialRow (fderiv ℝ R z) j)+
      (t^2*C.scalar (dist o) z^2)*
        (differentialRow (fderiv ℝ G z) i*differentialRow (fderiv ℝ G z) j))
    exact (((measurable_const.sub (hgm.const_mul t)).pow_const 2).mul (hP i j) |>.sub
      ((((measurable_const.sub (hgm.const_mul t)).mul_const t).mul hrm).mul
        (((hRd i).mul (hGd j)).add ((hGd i).mul (hRd j))))).add
      (((hrm.pow_const 2).const_mul (t^2)).mul ((hGd i).mul (hGd j)))
  have hJ : Measurable J := by
    dsimp [J]
    apply Measurable.sqrt
    simp only [Matrix.det_apply']
    apply Finset.measurable_sum
    intro σ _
    apply Measurable.const_mul
    exact Finset.measurable_prod Finset.univ (fun i _ => hEntry (σ i) i)
  apply hJ.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR,
    ae_fderivWithin_eq_fderiv_extension volume C.borel hG heG] with z hRz hGz
  simp only [J,radialJacobian,hRz,hGz]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma ae_scalar_row_quadratic_bound
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ z ∂volume.restrict C.domain, ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar u) C.domain z) ⬝ᵥ v)^2 ≤
        (K:ℝ)^2*(v ⬝ᵥ (polarizationMatrix (p z)
          (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).mulVec v) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  have hrow : ∀ᵐ z ∂volume.restrict C.domain, ∀ v,
      |fderivWithin ℝ (C.scalar u) C.domain z v| ≤ K*p z v :=
    MetricDifferentiation.ae_scalarOn_derivative_bound volume C.borel hL
      (hp.mono fun z hz => hz.1) hu
  filter_upwards [hp,hrow] with z hpz hrowz v
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
  have hquad : v ⬝ᵥ (polarizationMatrix (p z) b).mulVec v = p z (WithLp.toLp 2 v)^2 := by
    simpa only [hrepr] using
      polarizationMatrix_quadratic b (p z) hpz.2.2 hpz.2.1 (WithLp.toLp 2 v)
  rw [differentialRow_dot,hquad]
  have hh := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg K.coe_nonneg (apply_nonneg (p z) _))).2 (hrowz (WithLp.toLp 2 v))
  simpa only [sq_abs,mul_pow] using hh

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
theorem radialJacobian_le_intrinsic_majorant
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ᵐ z ∂volume.restrict C.domain,
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ≤ A*Real.sqrt (polarizationMatrix (p z)
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  obtain ⟨A,hA,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := Fin k) B hB0
  refine ⟨A+1,by linarith,?_⟩
  intro t ht
  filter_upwards [hp,ae_restrict_mem C.borel,
    C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
    C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hR hG
  let P := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hP : P.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ P.mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
  have hα : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    have hh := hR v
    simp only [NNReal.coe_one,one_pow,one_mul] at hh
    exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
  have hγ : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    exact (hG v).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hh := hbound P hP (C.scalar g z) (C.scalar (dist o) z)
    (by simpa only [C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩))
    (by simpa only [C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩))
    _ _ hα hγ t ht
  have hpos : 0 < Real.sqrt P.det := Real.sqrt_pos.2 hP.det_pos
  apply (div_le_iff₀ hpos).1
  change C.radialJacobian _ o g t z / Real.sqrt P.det ≤ A+1
  have hAt : A*t ≤ A := (mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one A)
  change |C.radialJacobian (fun z => polarizationMatrix (p z)
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z / Real.sqrt P.det-1| ≤ A*t at hh
  have hs := (le_abs_self _).trans hh
  linarith

end CAT0Fillings.IntegerChart
end
end

end OAI
