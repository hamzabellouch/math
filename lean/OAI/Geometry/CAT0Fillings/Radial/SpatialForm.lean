import Mathlib

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
lemma det_updateRow_identity (j : ι) (v : ι → ℝ) :
    (Matrix.updateRow (1 : Matrix ι ι ℝ) j v).det = v j := by
  have he : (∑ i : ι, v i • (1 : Matrix ι ι ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

theorem hasDerivAt_det_at_identity {A : ℝ → Matrix ι ι ℝ}
    {B : Matrix ι ι ℝ} {t : ℝ} (hA : A t = 1) (hd : HasDerivAt A B t) :
    HasDerivAt (fun s => (A s).det) B.trace t := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩
  have hD := (D.hasFDerivAt (A t)).comp_hasDerivAt t hd
  change HasDerivAt (fun s => (A s).det) (D.linearDeriv (A t) B) t at hD
  have hv : D.linearDeriv (fun i j => A t i j) (fun i j => B i j) = B.trace := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, (Matrix.updateRow (A t) i (B i)).det) = B.trace
    rw [hA]
    simp only [det_updateRow_identity,Matrix.trace,Matrix.diag]
  exact hD.congr_deriv hv

def spatialRadialForm (g r t : ℝ) (α γ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (1-t*g)^2 * (if i=j then 1 else 0) -
    (1-t*g)*t*r*(α i*γ j+γ i*α j) + t^2*r^2*γ i*γ j

omit [Fintype ι] in
lemma spatialRadialForm_zero (g r : ℝ) (α γ : ι → ℝ) :
    spatialRadialForm g r 0 α γ = 1 := by
  ext i j
  simp [spatialRadialForm,Matrix.one_apply]

lemma spatialRadialForm_hasDerivAt_zero (g r : ℝ) (α γ : ι → ℝ) :
    HasDerivAt (fun t => spatialRadialForm g r t α γ)
      (Matrix.of fun i j => -2*g*(if i=j then 1 else 0)-r*(α i*γ j+γ i*α j)) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hl := (hasDerivAt_const (0:ℝ) 1).sub ((hasDerivAt_id (0:ℝ)).mul_const g)
  have he := (((hl.fun_pow 2).mul_const (if i=j then 1 else 0)).sub
    (((hl.mul (hasDerivAt_id (0:ℝ))).mul_const r).mul_const (α i*γ j+γ i*α j))).add
      ((((hasDerivAt_id (0:ℝ)).fun_pow 2).mul_const (r^2)).mul_const (γ i*γ j))
  convert he using 1
  · ext t
    simp only [spatialRadialForm,Matrix.of_apply,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,id_eq]
    ring
  · simp

theorem spatialRadialForm_sqrt_det_hasDerivAt_zero (g r : ℝ) (α γ : ι → ℝ) :
    HasDerivAt (fun t => Real.sqrt (spatialRadialForm g r t α γ).det)
      (-((Fintype.card ι : ℝ)*g+r*∑ i, α i*γ i)) 0 := by
  have hd := hasDerivAt_det_at_identity (spatialRadialForm_zero g r α γ)
    (spatialRadialForm_hasDerivAt_zero g r α γ)
  have hs := hd.sqrt (by simp [spatialRadialForm_zero])
  convert hs using 1
  simp only [spatialRadialForm_zero,Matrix.det_one,Real.sqrt_one,Matrix.trace,
    Matrix.diag,Matrix.of_apply,ite_true, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [←Finset.mul_sum]
  have hh : (∑ i, (α i*γ i+γ i*α i)) = 2*(∑ i, α i*γ i) := by
    rw [Finset.sum_add_distrib]
    simp only [mul_comm (γ _) (α _)]
    ring
  rw [hh]
  ring

end CAT0Fillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
