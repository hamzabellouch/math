import Mathlib
import OAI.Analysis.AffineBernstein.ParametricVariationAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/
def newtonTensor (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j =>
  fderiv ℝ (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j) (fun l m => A l m)
    (fun l m => (1 : Matrix ι ι ℝ) l m)

theorem contDiff_newtonTensor_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => newtonTensor (Matrix.of A) i j) := by
  exact ((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem newtonTensor_eq_deriv (A : Matrix ι ι ℝ) (i j : ι) :
    newtonTensor A i j = deriv (fun t : ℝ => (A + t • 1).adjugate i j) 0 := by
  have hd : HasDerivAt (fun t : ℝ => fun l m => (A + t • 1) l m)
      (fun l m => (1 : Matrix ι ι ℝ) l m) 0 := by
    apply hasDerivAt_pi.mpr
    intro l
    apply hasDerivAt_pi.mpr
    intro m
    change HasDerivAt (fun t : ℝ => A l m + t * (1 : Matrix ι ι ℝ) l m)
      ((1 : Matrix ι ι ℝ) l m) 0
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const
      ((1 : Matrix ι ι ℝ) l m)).const_add (A l m)
  have hA : HasFDerivAt (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j)
      (fderiv ℝ (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j) (fun l m => A l m))
      (fun l m => (A + (0 : ℝ) • 1) l m) := by
    simpa using ((contDiff_adjugate_entry i j).differentiable (by simp) (fun l m => A l m)).hasFDerivAt
  have hh := hA.comp_hasDerivAt 0 hd
  have hη (C : Matrix ι ι ℝ) : Matrix.of (fun l m => C l m) = C := by
    ext l m
    rfl
  simpa only [newtonTensor, Function.comp_def, hη] using hh.deriv.symm

theorem newtonTensor_isSymm {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    (newtonTensor A).IsSymm := by
  have he (t : ℝ) : (A + t • (1 : Matrix ι ι ℝ)).adjugate.IsSymm :=
    (hA.add (Matrix.isSymm_one.smul t)).adjugate
  ext i j
  simp only [Matrix.transpose_apply, newtonTensor_eq_deriv]
  congr 1
  funext t
  exact congrFun (congrFun (he t) i) j

end AffineBernstein
end

end OAI
