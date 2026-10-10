import OAI.Analysis.LiebThirring.OperatorForm

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

lemma shiftedFormMap_bijective {W : ℝ → ℝ} (d : PotentialData W) :
    Function.Bijective (shiftedFormMap d) :=
  coercive_bijective _ (by norm_num : (0:ℝ) < 3/4) (shiftedFormMap_coercive d)

def formEquiv {W : ℝ → ℝ} (d : PotentialData W) : H1C ≃L[ℂ] H1C :=
  ContinuousLinearEquiv.ofBijective (shiftedFormMap d)
    (LinearMap.ker_eq_bot.mpr (shiftedFormMap_bijective d).1)
    (LinearMap.range_eq_top.mpr (shiftedFormMap_bijective d).2)

def solveL {W : ℝ → ℝ} (d : PotentialData W) : L2C →L[ℂ] H1C :=
  (formEquiv d).symm.toContinuousLinearMap.comp valL.adjoint

@[simp] lemma shifted_solve {W : ℝ → ℝ} (d : PotentialData W) (f : L2C) :
    shiftedFormMap d (solveL d f) = valL.adjoint f :=
  (formEquiv d).apply_symm_apply _

@[simp] lemma solve_shifted {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) :
    (formEquiv d).symm (shiftedFormMap d u) = u :=
  (formEquiv d).symm_apply_apply u

def resolvent {W : ℝ → ℝ} (d : PotentialData W) : L2C →L[ℂ] L2C := valL.comp (solveL d)

lemma val_adjoint_injective : Function.Injective valL.adjoint := by
  intro f g h
  apply valL_dense.eq_of_inner_left ℂ
  rintro z ⟨u,rfl⟩
  rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left,h]

lemma resolvent_injective {W : ℝ → ℝ} (d : PotentialData W) :
    Function.Injective (resolvent d) :=
  valL_injective.comp ((formEquiv d).symm.injective.comp val_adjoint_injective)

lemma resolvent_symmetric {W : ℝ → ℝ} (d : PotentialData W) :
    (resolvent d).IsSymmetric := by
  intro f g
  change inner ℂ (valL (solveL d f)) g = inner ℂ f (valL (solveL d g))
  rw [← ContinuousLinearMap.adjoint_inner_right valL (solveL d f) g,
    ← ContinuousLinearMap.adjoint_inner_left valL (solveL d g) f,
    ← shifted_solve d f,← shifted_solve d g]
  exact ((shiftedFormMap_symmetric d) (solveL d f) (solveL d g)).symm

lemma resolvent_dense {W : ℝ → ℝ} (d : PotentialData W) :
    Dense (Set.range (resolvent d)) := by
  have hk : (resolvent d).ker = ⊥ := LinearMap.ker_eq_bot.mpr (resolvent_injective d)
  have he := (resolvent d).orthogonal_ker
  rw [hk,Submodule.bot_orthogonal_eq_top,(resolvent_symmetric d).clm_adjoint_eq] at he
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℂ L2C ↦ (S : Set L2C)) he.symm

lemma solve_form {W : ℝ → ℝ} (d : PotentialData W) (f : L2C) (v : H1C) :
    schrodingerForm W (toH1 v) (toH1 (solveL d f))+
      (d.b+1 : ℂ)*inner ℂ (valL v) (resolvent d f) = inner ℂ (valL v) f := by
  have h := congrArg (fun u ↦ inner ℂ v u) (shifted_solve d f)
  rw [shiftedFormMap_inner,ContinuousLinearMap.adjoint_inner_right] at h
  rw [form_eq_inner]
  exact h

end SharpLiebThirring.OperatorProof

end

end OAI
