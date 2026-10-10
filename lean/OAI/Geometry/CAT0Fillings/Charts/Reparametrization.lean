import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Scalar
import OAI.Geometry.CAT0Fillings.Charts.Orientation

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))
noncomputable def reparam : IntegerChart X k where
  domain := f '' C.domain
  borel := C.borel.image_of_continuousOn_injOn hf.continuousOn (antilipschitzOn_injOn ha)
  bounded := by
    apply Metric.isBounded_iff.mpr
    refine ⟨(K : ℝ) * diam C.domain,?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hf.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem C.bounded hx hy) K.coe_nonneg)
  param := fun y => C.param ⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩
  bilipschitz := by
    obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
    refine ⟨J * L,K * U,?_,?_⟩
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have h := (lipschitzOn_invFunOn ha).dist_le_mul x x.property y y.property
      exact (hJ.dist_le_mul _ _).trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left h J.coe_nonneg))
    · apply AntilipschitzWith.of_le_mul_dist
      intro x y
      have hx := Function.invFunOn_mem x.property
      have hy := Function.invFunOn_mem y.property
      have h := hf.dist_le_mul _ hx _ hy
      rw [Function.invFunOn_eq x.property,Function.invFunOn_eq y.property] at h
      exact h.trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left (hU.le_mul_dist ⟨_,hx⟩ ⟨_,hy⟩) K.coe_nonneg))
  multiplicity := fun y => C.multiplicity (Function.invFunOn f C.domain y) *
    differentialOrientation (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det
  integrable := integrableOn_oriented_multiplicity_image volume C.borel hf
    (antilipschitzOn_injOn ha) C.integrable

lemma reparam_scalar {b : X → ℝ} {x : Euc k} (hx : x ∈ C.domain) :
    (C.reparam f hf ha).scalar b (f x) = C.scalar b x := by
  have hfx : f x ∈ (C.reparam f hf ha).domain := ⟨x,hx,rfl⟩
  rw [(C.reparam f hf ha).scalar_eq hfx,C.scalar_eq hx]
  change b (C.param ⟨Function.invFunOn f C.domain (f x),_⟩) = b (C.param ⟨x,hx⟩)
  congr 2
  apply Subtype.ext
  exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn hx

lemma reparam_image : (C.reparam f hf ha).image = C.image := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨⟨f z,⟨z,z.property,rfl⟩⟩,?_⟩
    change C.param ⟨Function.invFunOn f C.domain (f z),_⟩ = C.param z
    congr 1
    apply Subtype.ext
    exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn z.property

end IntegerChart

lemma row_det_comp {k : ℕ} (rows : Fin k → Euc k →L[ℝ] ℝ) (A : Euc k →L[ℝ] Euc k) :
    Matrix.det (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      Matrix.det (fun i j => rows i (EuclideanSpace.single j 1)) * A.det := by
  let B := EuclideanSpace.basisFun (Fin k) ℝ
  have hm : (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      (show Matrix (Fin k) (Fin k) ℝ from fun i j => rows i (EuclideanSpace.single j 1)) * LinearMap.toMatrix B.toBasis B.toBasis A.toLinearMap := by
    ext i j
    rw [Matrix.mul_apply]
    have h := congrArg (rows i) (B.sum_repr (A (EuclideanSpace.single j 1)))
    simp only [_root_.map_sum,map_smul,smul_eq_mul] at h
    simpa only [B,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr,OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis,ContinuousLinearMap.coe_coe,mul_comm] using h.symm
  rw [hm,Matrix.det_mul,LinearMap.det_toMatrix]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))

lemma reparam_jacobian_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict C.domain, C.jacobian π x =
      (C.reparam f hf ha).jacobian π (f x) * (fderivWithin ℝ f C.domain x).det := by
  have hr : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
        (fderivWithin ℝ ((C.reparam f hf ha).scalar (π i)) (f '' C.domain) (f x)).comp
          (fderivWithin ℝ f C.domain x) := by
    intro i
    obtain ⟨J,hJ⟩ := hπ i
    obtain ⟨U,V,hU,_⟩ := (C.reparam f hf ha).bilipschitz
    have hc := ae_fderivWithin_comp_bilipschitzOn volume C.borel hf ha
      ((C.reparam f hf ha).scalar_lipschitzOn hU hJ)
    filter_upwards [hc,ae_restrict_mem C.borel] with x hx hxs
    have heq : EqOn ((C.reparam f hf ha).scalar (π i) ∘ f) (C.scalar (π i)) C.domain :=
      fun z hz => C.reparam_scalar f hf ha hz
    rwa [fderivWithin_congr' heq hxs] at hx
  filter_upwards [ae_all_iff.mpr hr] with x hx
  unfold jacobian
  simp_rw [hx,ContinuousLinearMap.comp_apply]
  exact row_det_comp _ _

variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma reparam_action : (C.reparam f hf ha).action = C.action := by
  funext b π
  by_cases hbπ : Admissible b π
  · simp only [action,ite_eq_left hbπ]
    change (∫ y in f '' C.domain,
      ((C.multiplicity (Function.invFunOn f C.domain y) * differentialOrientation
        (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det : ℤ) : ℝ) *
        (C.reparam f hf ha).scalar b y * (C.reparam f hf ha).jacobian π y) = _
    simp_rw [mul_assoc]
    rw [signed_lipschitzOn_changeVariables volume C.borel hf (antilipschitzOn_injOn ha)]
    apply integral_congr_ae
    filter_upwards [C.reparam_jacobian_ae f hf ha hbπ.2,ae_restrict_mem C.borel] with x hx hxs
    rw [C.reparam_scalar f hf ha hxs,hx]
    ring
  · simp only [action,ite_eq_right hbπ]

omit [BorelSpace X] in
lemma reparam_isMetricCurrent (hC : IsMetricCurrent C.action) :
    IsMetricCurrent (C.reparam f hf ha).action := by
  rwa [C.reparam_action f hf ha]

omit [BorelSpace X] in
lemma reparam_mass : mass (C.reparam f hf ha).action = mass C.action := by
  rw [C.reparam_action f hf ha]

end IntegerChart
end CAT0Fillings
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
