import Mathlib
import OAI.Geometry.CAT0Fillings.Geometry.Determinant
import OAI.Geometry.CAT0Fillings.Radial.SpatialForm

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
omit [Fintype ι] in
lemma spatialRadialForm_rankOne_decomposition (g r t : ℝ) (α γ : ι → ℝ) :
    spatialRadialForm g r t α γ =
      (1-t*g)^2 • (1-vecMulVec α α) +
        vecMulVec ((1-t*g) • α-(t*r) • γ) ((1-t*g) • α-(t*r) • γ) := by
  ext i j
  simp only [spatialRadialForm,Matrix.of_apply,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.one_apply,Matrix.vecMulVec_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma dotProduct_vecMulVec_self (u v : ι → ℝ) :
    v ⬝ᵥ (vecMulVec u u).mulVec v = (u ⬝ᵥ v)^2 := by
  rw [Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_smul,smul_eq_mul,
    dotProduct_comm v u,pow_two]

theorem spatialRadialForm_posSemidef (g r t : ℝ) (α γ : ι → ℝ)
    (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ v) :
    (spatialRadialForm g r t α γ).PosSemidef := by
  have hQ : (1-vecMulVec α α : Matrix ι ι ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub Matrix.isHermitian_one
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  rw [spatialRadialForm_rankOne_decomposition]
  apply Matrix.PosSemidef.add (hQ.smul (sq_nonneg _))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    ((1-t*g) • α-(t*r) • γ)

lemma spatialRadialForm_quadratic (g r t : ℝ) (α γ v : ι → ℝ) :
    v ⬝ᵥ (spatialRadialForm g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ v-(α ⬝ᵥ v)^2) := by
  rw [spatialRadialForm_rankOne_decomposition,Matrix.add_mulVec,dotProduct_add,
    dotProduct_vecMulVec_self,Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,
    Matrix.one_mulVec,dotProduct_sub,dotProduct_vecMulVec_self,
    sub_dotProduct,smul_dotProduct,smul_dotProduct]
  simp only [smul_eq_mul]
  ring

theorem abs_det_le_spatialRadialJacobian {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℝ) (g r t : ℝ) (α γ : Fin n → ℝ)
    (hα : ∀ v : Fin n → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ v)
    (hL : ∀ i v, (L i ⬝ᵥ v)^2 ≤
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ v-(α ⬝ᵥ v)^2)) :
    |L.det| ≤ Real.sqrt (spatialRadialForm g r t α γ).det := by
  apply abs_det_le_sqrt_det_of_posSemidef L _ (spatialRadialForm_posSemidef g r t α γ hα)
  intro i v
  have hn : 0 ≤ v ⬝ᵥ (spatialRadialForm g r t α γ).mulVec v := by
    rw [spatialRadialForm_quadratic]
    exact (sq_nonneg _).trans (hL i v)
  apply (Real.le_sqrt (abs_nonneg _) hn).2
  simpa only [sq_abs,spatialRadialForm_quadratic] using hL i v

end CAT0Fillings

end
end

end OAI
