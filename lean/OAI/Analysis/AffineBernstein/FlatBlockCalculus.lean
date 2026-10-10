import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def flatBlockHessian (f : E → ℝ) (v : ι → E) (x : E) : Matrix ι ι ℝ :=
  fun i j => dirDeriv (v i) (dirDeriv (v j) f) x

omit [DecidableEq ι] in
lemma contDiffAt_flatBlockHessian {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (v : ι → E) : ContDiffAt ℝ ∞ (fun y i j => flatBlockHessian f v y i j) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_dirDeriv (contDiffAt_dirDeriv hf (v j)) (v i)))

lemma contDiffAt_adjugate_entries {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ (fun y i j => A y i j) x) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  change ContDiffAt ℝ ∞ (fun y => continuousDetRows (fun l m => (A y).updateRow j (Pi.single i 1) l m)) x
  apply (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simp only [Matrix.updateRow_ne hl]
    exact (contDiffAt_pi.mp hA) l

omit [Fintype ι] [DecidableEq ι] in
lemma flatBlockHessian_isSymm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (v : ι → E) : (flatBlockHessian f v x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact dirDeriv_comm hf (v j) (v i)

lemma flatBlockHessian_adjugate_row_divergence {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : ι → E) (i : ι) :
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate i j) x) = 0 := by
  let F : ι → E → ℝ := fun i => dirDeriv (v i) f
  have hF (l : ι) : ContDiffAt ℝ 2 (F l) x :=
    (contDiffAt_dirDeriv hf (v l)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he (y : E) : jacobianRows F v y = (flatBlockHessian f v y).transpose := rfl
  simpa only [he,← Matrix.adjugate_transpose,Matrix.transpose_apply,dirDeriv] using
    piola_identity F v x hF i

lemma flatBlockHessian_adjugate_divergence {W : Set E} (hW : IsOpen W)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f W) (v : ι → E) {x : E} (hx : x ∈ W) (i : ι) :
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate i j) x) = 0 ∧
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate j i) x) = 0 := by
  have hr := flatBlockHessian_adjugate_row_divergence (hf.contDiffAt (hW.mem_nhds hx)) v i
  refine ⟨hr,?_⟩
  have he (j : ι) : (fun y => (flatBlockHessian f v y).adjugate j i) =ᶠ[𝓝 x]
      (fun y => (flatBlockHessian f v y).adjugate i j) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact ((flatBlockHessian_isSymm (hf.contDiffAt (hW.mem_nhds hy)) v).adjugate.apply i j)
  change (∑ j, fderiv ℝ (fun y => (flatBlockHessian f v y).adjugate j i) x (v j)) = 0
  simp_rw [(he _).fderiv_eq]
  exact hr

end AffineBernstein
end

end OAI
