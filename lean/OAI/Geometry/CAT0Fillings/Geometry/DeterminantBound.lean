import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Geometry.Determinant
import OAI.Geometry.CAT0Fillings.Geometry.HilbertDifferential

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
open Set MeasureTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma polarizationMatrix_quadratic_semidefinite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : E) :
    (b.repr v) ⬝ᵥ (polarizationMatrix p b).mulVec (b.repr v) = (p v)^2 := by
  obtain ⟨B,_,hdiag,hpol⟩ := exists_bilinForm_of_seminorm_parallelogram p hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq,←hdiag v]
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v v).symm

lemma polarizationMatrix_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    (polarizationMatrix p b).PosSemidef := by
  obtain ⟨B,hB,_,hpol⟩ := exists_bilinForm_of_seminorm_parallelogram p hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [heq,Matrix.isHermitian_iff_isSymm]
    exact (B.isSymm_toMatrix_iff_isSymm b).2 hB
  · intro v
    have hrepr : b.repr (b.equivFun.symm v) = v := b.equivFun.apply_symm_apply v
    have h := polarizationMatrix_quadratic_semidefinite b p hpara (b.equivFun.symm v)
    rw [hrepr] at h
    simpa only [star_trivial,h] using sq_nonneg (p (b.equivFun.symm v))

end CAT0Fillings
namespace CAT0Fillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

theorem exists_lipschitz_matrix_determinant_bound {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsf : volume s ≠ (∞ : ℝ≥0∞))
    {f : s → X} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ P : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, Measurable (fun x => P x i j)) ∧
      (∀ᵐ x ∂volume.restrict s, (P x).PosSemidef) ∧
      (∀ᵐ x ∂volume.restrict s, Real.sqrt (P x).det ≤ (K : ℝ)^n) ∧
      ∀ π : Fin n → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
        ∀ᵐ x ∂volume.restrict s,
          |(Matrix.of fun i j =>
            fderivWithin ℝ (scalarOn f (π i)) s x (EuclideanSpace.single j 1)).det| ≤
              Real.sqrt (P x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨p,hpm,hpLip,hae⟩ := exists_hilbertian_lipschitz_differential volume hs hsf hf hQ
  refine ⟨fun x => polarizationMatrix (p x) b,measurable_polarizationMatrix p b hpm,?_,?_,?_⟩
  · filter_upwards [hae] with x hx
    exact polarizationMatrix_posSemidef b (p x) hx.2
  · filter_upwards [hae] with x hx
    apply sqrt_det_le_pow_of_quadratic_bound _
      (polarizationMatrix_posSemidef b (p x) hx.2) K.coe_nonneg
    intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hrepr : b.repr w = v := by ext j; simp [b,w]
    have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
      simpa only [hrepr] using polarizationMatrix_quadratic_semidefinite b (p x) hx.2 w
    rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
    simpa only [dist_zero_right,map_zero,Real.norm_eq_abs, abs_of_nonneg (apply_nonneg (p x) w)] using (hpLip x).dist_le_mul w 0
  intro π hπ
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := hae.mono fun x hx => hx.1
  have hrows : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ p x v := by
    rw [eventually_all]
    intro i
    simpa only [NNReal.coe_one,one_mul] using ae_scalarOn_derivative_bound volume hs hf hdiff (hπ i)
  filter_upwards [hae,hrows] with x hx hrow
  apply abs_det_le_sqrt_det_of_posSemidef _ _ (polarizationMatrix_posSemidef b (p x) hx.2)
  intro i v
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by
    ext j
    simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic_semidefinite b (p x) hx.2 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
  convert hrow i w using 1
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = w := by
    convert b.sum_repr w using 1
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,_root_.map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.of_apply, dotProduct, mul_comm]
end CAT0Fillings.MetricDifferentiation

end
end

end OAI
