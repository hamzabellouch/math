import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Radial.ScalarDerivative
import OAI.Geometry.CAT0Fillings.Radial.MetricBound

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

namespace CAT0Fillings
open Filter MeasureTheory Set Metric Matrix
open scoped Topology NNReal BigOperators

noncomputable def differentialRow {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) : Fin n → ℝ :=
  fun j => L (EuclideanSpace.single j 1)

lemma differentialRow_dot {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v : Fin n → ℝ) :
    differentialRow L ⬝ᵥ v = L (WithLp.toLp 2 v) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = WithLp.toLp 2 v := by
    convert b.sum_repr (WithLp.toLp 2 v) using 1
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,_root_.map_sum]
  simp only [differentialRow,map_smul,smul_eq_mul,dotProduct,mul_comm]

theorem radial_test_det_le {n : ℕ} {X : Type*} [MetricSpace X]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hxs : x ∈ s)
    (hx : Tendsto (fun t => volume (s ∩ closedBall x t) / volume (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : EuclideanSpace ℝ (Fin n) → X) (o : X)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (hpos : ∀ v, p v = 0 ↔ v = 0)
    (hpar : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (htg : ∀ y ∈ s, 1-t*g y ∈ Icc (0:ℝ) 1)
    (α γ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) α s x)
    (hγ : HasFDerivWithinAt g γ s x)
    (F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivWithinAt (F i) (L i) s x)
    (u : Fin n → X → ℝ) (hu : ∀ i, LipschitzWith 1 (u i))
    (hF : ∀ i y, y ∈ s → F i y = u i (seg o (f y) (1-t*g y))) :
    |(Matrix.of fun i j => differentialRow (L i) j).det| ≤
      Real.sqrt (metricSpatialRadialForm
        (polarizationMatrix p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (g x) (dist o (f x)) t (differentialRow α) (differentialRow γ)).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hG := polarizationMatrix_posDef b p hpos hpar
  have hquadratic (v : Fin n → ℝ) :
      v ⬝ᵥ (polarizationMatrix p b).mulVec v = p (WithLp.toLp 2 v)^2 := by
    have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
    simpa only [hrepr] using polarizationMatrix_quadratic b p hpos hpar (WithLp.toLp 2 v)
  have hcontract (v : Fin n → ℝ) :
      (differentialRow α ⬝ᵥ v)^2 ≤ v ⬝ᵥ (polarizationMatrix p b).mulVec v := by
    rw [hquadratic,differentialRow_dot]
    have hr := scalar_derivative_bound_of_metric_differential volume hx hα hp
      (K := 1) (by
        intro y _
        simpa only [one_mul,dist_comm o] using abs_dist_sub_le (f y) (f x) o)
      (WithLp.toLp 2 v)
    have hh := (sq_le_sq₀ (abs_nonneg _) (apply_nonneg p _)).2 (by simpa using hr)
    simpa only [sq_abs] using hh
  apply abs_det_le_metricSpatialRadialJacobian _ _ _ _ _ _ _ hG.posSemidef hcontract
  intro i v
  have hr := radial_scalar_derivative_sq_le volume seg hcomp hxs hx f o p hp htg hα
    ((hγ.const_mul t).const_sub 1) (hL i) (hu i) (hF i) (WithLp.toLp 2 v)
  change (differentialRow (L i) ⬝ᵥ v)^2 ≤ _
  rw [differentialRow_dot,hquadratic,differentialRow_dot,differentialRow_dot]
  convert hr using 1
  simp only [_root_.neg_apply,_root_.smul_apply,smul_eq_mul]
  ring

end CAT0Fillings
end
end

end OAI
