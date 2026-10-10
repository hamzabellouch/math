import Mathlib
import OAI.Analysis.AffineBernstein.SmoothCoefficients

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A fixed-direction derivative, used only as notation for the actual Fréchet derivative. -/
def dirDeriv (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem dirDeriv_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dirDeriv v (fun y => f y * g y) x = dirDeriv v f x * g x + f x * dirDeriv v g x := by
  simp only [dirDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

theorem dirDeriv_sum (f : ι → E → ℝ) {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (v : E) :
    dirDeriv v (fun y => ∑ i, f i y) x = ∑ i, dirDeriv v (f i) x := by
  simp only [dirDeriv, fderiv_fun_sum (fun i _ => hf i), sum_apply]

/-- The differential part of the double integration by parts. Both zero
cofactor divergences are used; they will be supplied by the proved Piola identity. -/
theorem double_divergence_weighted {Ω : Set E} (hΩ : IsOpen Ω)
    (U : E → ι → ι → ℝ) (w : E → ℝ) (e : ι → E)
    (hU : ∀ x ∈ Ω, ∀ i j, ContDiffAt ℝ ∞ (fun y => U y i j) x)
    (hw : ∀ x ∈ Ω, ContDiffAt ℝ ∞ w x)
    (hrow : ∀ x ∈ Ω, ∀ i, (∑ j, dirDeriv (e j) (fun y => U y i j) x) = 0)
    (hcol : ∀ x ∈ Ω, ∀ j, (∑ i, dirDeriv (e i) (fun y => U y i j) x) = 0)
    {x : E} (hx : x ∈ Ω) :
    (∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (fun y => w y * U y i j)) x) =
      ∑ j, ∑ i, U x i j * dirDeriv (e j) (dirDeriv (e i) w) x := by
  have hfirst (y : E) (hy : y ∈ Ω) (j : ι) :
      (∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) =
        ∑ i, dirDeriv (e i) w y * U y i j := by
    calc
      _ = ∑ i, (dirDeriv (e i) w y * U y i j +
          w y * dirDeriv (e i) (fun z => U z i j) y) :=
        Finset.sum_congr rfl fun i _ => dirDeriv_mul
          ((hw y hy).differentiableAt (by simp)) ((hU y hy i j).differentiableAt (by simp)) _
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol y hy j, mul_zero, add_zero]
  have he (j : ι) : (fun y => ∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) =ᶠ[nhds x]
      (fun y => ∑ i, dirDeriv (e i) w y * U y i j) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hfirst y hy j
  have hsecond (j : ι) :
      (∑ i, dirDeriv (e j) (dirDeriv (e i) (fun y => w y * U y i j)) x) =
        ∑ i, (dirDeriv (e j) (dirDeriv (e i) w) x * U x i j +
          dirDeriv (e i) w x * dirDeriv (e j) (fun y => U y i j) x) := by
    calc
      _ = dirDeriv (e j) (fun y => ∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) x := by
        symm
        apply dirDeriv_sum
        intro i
        exact (contDiffAt_dirDeriv ((hw x hx).mul (hU x hx i j)) _).differentiableAt (by simp)
      _ = dirDeriv (e j) (fun y => ∑ i, dirDeriv (e i) w y * U y i j) x :=
        congrArg (fun L : E →L[ℝ] ℝ => L (e j)) (he j).fderiv_eq
      _ = ∑ i, dirDeriv (e j) (fun y => dirDeriv (e i) w y * U y i j) x := by
        apply dirDeriv_sum
        intro i
        exact ((contDiffAt_dirDeriv (hw x hx) _).mul (hU x hx i j)).differentiableAt (by simp)
      _ = _ := Finset.sum_congr rfl fun i _ =>
        dirDeriv_mul ((contDiffAt_dirDeriv (hw x hx) _).differentiableAt (by simp))
          ((hU x hx i j).differentiableAt (by simp)) _
  have hzero : (∑ j, ∑ i, dirDeriv (e i) w x *
      dirDeriv (e j) (fun y => U y i j) x) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.mul_sum, hrow x hx i, mul_zero]
  calc
    _ = ∑ j, ∑ i, (dirDeriv (e j) (dirDeriv (e i) w) x * U x i j +
          dirDeriv (e i) w x * dirDeriv (e j) (fun y => U y i j) x) :=
      Finset.sum_congr rfl fun j _ => hsecond j
    _ = ∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) w) x * U x i j := by
      simp only [Finset.sum_add_distrib]
      rw [hzero, add_zero]
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

end WeightedDivergence

/-- The exact maximal-graph operator is the double divergence of its variational coefficient. -/
theorem affine_operator_eq_double_divergence {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) {x : Space n} (hx : x ∈ Ω) :
    (∑ j, ∑ i, dirDeriv (coordinateVector n j) (dirDeriv (coordinateVector n i)
      (fun y => affineWeight u y * cofactorHessian u y i j)) x) =
      ∑ i, ∑ j, cofactorHessian u x i j * hessian (affineWeight u) x i j := by
  have hu3 : ContDiffOn ℝ 3 u Ω :=
    hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hdiv := cofactorHessian_divergence hΩ u hu3 hpos
  rw [double_divergence_weighted hΩ (fun y i j => cofactorHessian u y i j)
    (affineWeight u) (coordinateVector n)
    (fun y hy => contDiffAt_cofactorHessian_entry hΩ hu hpos hy)
    (fun y hy => contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy))
    (fun y hy i => (hdiv y hy i).1) (fun y hy j => (hdiv y hy j).2) hx]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(cofactorHessian_isSymm u x (hpos x hx)).apply i j]
  rfl

end AffineBernstein
end

end OAI
