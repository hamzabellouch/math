import Mathlib
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
open scoped BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma hasDerivAt_matrix_mul_const {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    {t : ℝ} (hd : HasDerivAt A B t) (G : Matrix ι ι ℝ) :
    HasDerivAt (fun s => A s*G) (B*G) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun l _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i)) l).mul_const (G l j)

theorem hasDerivAt_det_at_nonsingular {A : ℝ → Matrix ι ι ℝ}
    {B G : Matrix ι ι ℝ} {t : ℝ} (hA : A t = G) (hG : G.det ≠ 0)
    (hd : HasDerivAt A B t) :
    HasDerivAt (fun s => (A s).det) ((B*G⁻¹).trace*G.det) t := by
  have hid : A t*G⁻¹ = 1 := by rw [hA,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)]
  have h := (hasDerivAt_det_at_identity (A := fun s => A s*G⁻¹) hid (hasDerivAt_matrix_mul_const hd G⁻¹)).mul_const G.det
  have he : (fun s => (A s).det) = (fun s => (A s*G⁻¹).det*G.det) := by
    funext s
    rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    field_simp
  rw [he]
  exact h

def metricSpatialRadialForm (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) : Matrix ι ι ℝ :=
  (1-t*g)^2 • G-((1-t*g)*t*r) • (vecMulVec α γ+vecMulVec γ α)+
    (t^2*r^2) • vecMulVec γ γ

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_hasDerivAt_zero (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ) :
    HasDerivAt (fun t => metricSpatialRadialForm G g r t α γ)
      ((-2*g) • G-r • (vecMulVec α γ+vecMulVec γ α)) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hl := (hasDerivAt_const (0:ℝ) 1).sub ((hasDerivAt_id (0:ℝ)).mul_const g)
  have ht := hasDerivAt_id (0:ℝ)
  have h := (((hl.fun_pow 2).mul_const (G i j)).sub
    (((hl.mul ht).mul_const r).mul_const (α i*γ j+γ i*α j))).add
    (((ht.fun_pow 2).mul_const (r^2)).mul_const (γ i*γ j))
  convert h using 1
  · ext t
    simp [metricSpatialRadialForm,Matrix.vecMulVec_apply,mul_add]
  · simp [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,mul_add]

lemma trace_radial_matrix_derivative (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ)
    (hG : G.det ≠ 0) (hs : G⁻¹.IsSymm) :
    (((-2*g) • G-r • (vecMulVec α γ+vecMulVec γ α))*G⁻¹).trace =
      -2*((Fintype.card ι : ℝ)*g+r*(α ⬝ᵥ G⁻¹.mulVec γ)) := by
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG),
    Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_smul,Matrix.add_mul,Matrix.trace_add]
  have htr (u v : ι → ℝ) : (vecMulVec u v*G⁻¹).trace = u ⬝ᵥ G⁻¹.mulVec v := by
    rw [Matrix.vecMulVec_mul,Matrix.trace_vecMulVec]
    congr 1
    exact (Matrix.mulVec_transpose G⁻¹ v).symm.trans (congrArg (fun A => A.mulVec v) hs)
  rw [htr,htr]
  have hsym : γ ⬝ᵥ G⁻¹.mulVec α = α ⬝ᵥ G⁻¹.mulVec γ := by
    rw [dotProduct_mulVec,←Matrix.mulVec_transpose,hs,dotProduct_comm]
  rw [hsym]
  simp only [Matrix.trace_one]
  ring

theorem metricSpatialRadialForm_normalized_sqrt_det_hasDerivAt_zero
    (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ)
    (hG : G.PosDef) :
    HasDerivAt (fun t => Real.sqrt (metricSpatialRadialForm G g r t α γ).det /
      Real.sqrt G.det)
      (-((Fintype.card ι : ℝ)*g+r*(α ⬝ᵥ G⁻¹.mulVec γ))) 0 := by
  have hpos : 0 < G.det := hG.det_pos
  have hz : metricSpatialRadialForm G g r 0 α γ = G := by simp [metricSpatialRadialForm]
  have hd := hasDerivAt_det_at_nonsingular hz hpos.ne'
    (metricSpatialRadialForm_hasDerivAt_zero G g r α γ)
  have hs : G⁻¹.IsSymm := by
    have hi := hG.isHermitian.inv
    exact Matrix.isHermitian_iff_isSymm.mp hi
  rw [trace_radial_matrix_derivative G g r α γ hpos.ne' hs] at hd
  have h := (hd.sqrt (by rw [hz]; exact hpos.ne')).div_const (Real.sqrt G.det)
  apply h.congr_deriv
  rw [hz]
  have hsq := Real.sq_sqrt hpos.le
  have hn : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp
  rw [hsq]
end CAT0Fillings
end
end

end OAI
