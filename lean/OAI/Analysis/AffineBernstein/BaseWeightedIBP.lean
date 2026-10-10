import Mathlib
import OAI.Analysis.AffineBernstein.FlatBlockCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def flatCofactorTrace (f : E → ℝ) (v : ι → E) (g : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) g) x

def flatCofactorPair (f : E → ℝ) (v : ι → E) (g h : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) g x * dirDeriv (v i) h x

def flatCofactorFlux (f : E → ℝ) (v : ι → E) (β g : E → ℝ) (j : ι) (x : E) : ℝ :=
  ∑ i, (flatBlockHessian f v x).adjugate i j * β x * dirDeriv (v i) g x

lemma contDiffAt_flatCofactorFlux {f β g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hβ : ContDiffAt ℝ ∞ β x)
    (hg : ContDiffAt ℝ ∞ g x) (v : ι → E) (j : ι) :
    ContDiffAt ℝ ∞ (flatCofactorFlux f v β g j) x := by
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian hf v) i j).mul hβ).mul
    (contDiffAt_dirDeriv hg (v i))

lemma flatCofactorFlux_divergence {f β g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hβ : ContDiffAt ℝ ∞ β x)
    (hg : ContDiffAt ℝ ∞ g x) (v : ι → E) :
    (∑ j, dirDeriv (v j) (flatCofactorFlux f v β g j) x) =
      β x * flatCofactorTrace f v g x + flatCofactorPair f v β g x := by
  let C := fun i j y => (flatBlockHessian f v y).adjugate i j
  have hC (i j : ι) : ContDiffAt ℝ ∞ (C i j) x :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian hf v) i j
  have hd (j : ι) : dirDeriv (v j) (flatCofactorFlux f v β g j) x =
      ∑ i, (dirDeriv (v j) (C i j) x * (β x*dirDeriv (v i) g x) +
        C i j x * dirDeriv (v j) β x * dirDeriv (v i) g x +
        β x * (C i j x * dirDeriv (v j) (dirDeriv (v i) g) x)) := by
    change dirDeriv (v j) (fun y => ∑ i, C i j y*β y*dirDeriv (v i) g y) x = _
    rw [dirDeriv_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [dirDeriv_mul (((hC i j).mul hβ).differentiableAt (by simp))
        ((contDiffAt_dirDeriv hg (v i)).differentiableAt (by simp)),
        dirDeriv_mul ((hC i j).differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
      change (dirDeriv (v j) (C i j) x*β x+C i j x*dirDeriv (v j) β x)*dirDeriv (v i) g x +
        (C i j x*β x)*dirDeriv (v j) (dirDeriv (v i) g) x = _
      ring
    · intro i
      exact (((hC i j).mul hβ).mul (contDiffAt_dirDeriv hg (v i))).differentiableAt (by simp)
  have hz : (∑ j, ∑ i, dirDeriv (v j) (C i j) x * (β x*dirDeriv (v i) g x)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hrow (i : ι) : (∑ j, dirDeriv (v j) (C i j) x) = 0 :=
      flatBlockHessian_adjugate_row_divergence hf v i
    simp only [hrow,zero_mul,Finset.sum_const_zero]
  simp only [hd,Finset.sum_add_distrib,hz,zero_add,flatCofactorTrace,flatCofactorPair,
    ← Finset.mul_sum]
  ring

end AffineBernstein
end

end OAI
