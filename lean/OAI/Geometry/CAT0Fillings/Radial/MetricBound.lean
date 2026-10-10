import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.SpatialBound
import OAI.Geometry.CAT0Fillings.Radial.MetricDerivative

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
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
lemma metricSpatialRadialForm_rankOne_decomposition
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) :
    metricSpatialRadialForm G g r t α γ =
      (1-t*g)^2 • (G-vecMulVec α α) +
        vecMulVec ((1-t*g) • α-(t*r) • γ) ((1-t*g) • α-(t*r) • γ) := by
  ext i j
  simp only [metricSpatialRadialForm,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_quadratic
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ v : ι → ℝ) :
    v ⬝ᵥ (metricSpatialRadialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ G.mulVec v-(α ⬝ᵥ v)^2) := by
  rw [metricSpatialRadialForm_rankOne_decomposition,Matrix.add_mulVec,dotProduct_add,
    dotProduct_vecMulVec_self,Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,
    dotProduct_sub,dotProduct_vecMulVec_self,sub_dotProduct,smul_dotProduct,smul_dotProduct]
  simp only [smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_posSemidef
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosSemidef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    (metricSpatialRadialForm G g r t α γ).PosSemidef := by
  have hQ : (G-vecMulVec α α).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub hG.isHermitian
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  rw [metricSpatialRadialForm_rankOne_decomposition]
  apply Matrix.PosSemidef.add (hQ.smul (sq_nonneg _))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    ((1-t*g) • α-(t*r) • γ)

theorem abs_det_le_metricSpatialRadialJacobian {n : ℕ}
    (L G : Matrix (Fin n) (Fin n) ℝ) (g r t : ℝ) (α γ : Fin n → ℝ)
    (hG : G.PosSemidef)
    (hα : ∀ v : Fin n → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v)
    (hL : ∀ i v, (L i ⬝ᵥ v)^2 ≤
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ G.mulVec v-(α ⬝ᵥ v)^2)) :
    |L.det| ≤ Real.sqrt (metricSpatialRadialForm G g r t α γ).det := by
  apply abs_det_le_sqrt_det_of_posSemidef L _ (metricSpatialRadialForm_posSemidef G g r t α γ hG hα)
  intro i v
  have hn : 0 ≤ v ⬝ᵥ (metricSpatialRadialForm G g r t α γ).mulVec v := by
    rw [metricSpatialRadialForm_quadratic]
    exact (sq_nonneg _).trans (hL i v)
  apply (Real.le_sqrt (abs_nonneg _) hn).2
  simpa only [sq_abs,metricSpatialRadialForm_quadratic] using hL i v
end CAT0Fillings
end
end

end OAI
