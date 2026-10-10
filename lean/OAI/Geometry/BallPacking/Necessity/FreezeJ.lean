import Mathlib
import OAI.Geometry.BallPacking.Rigidity.CompatibleStructures

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

theorem compatible_standard_frame {n : ℕ} {J : End n} (hJ : Compatible J) :
    ∃ S : Phase n ≃L[ℝ] Phase n, ∀ v,
      S (J v)=Complex.I • S v := by
  obtain ⟨S,hS⟩ := cayleyP_invertible hJ (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 1)
  refine ⟨S,?_⟩
  intro v
  change (S : End n) (J v)=standardJ n ((S : End n) v)
  rw [hS]
  simp only [cayleyP_apply,one_smul,relativeOperator_apply,hJ.1,map_add,map_neg,
    standardJ_sq,neg_neg]
  abel

def centeredFrame {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (p : Phase n)
    (u : ℂ → Phase n) : ℂ → Phase n := fun z => S (u z-p)

def frozenCoefficient {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (J : End n)
    (B : ℂ → End n) : ℂ → End n := fun z =>
      S.toContinuousLinearMap.comp ((B z-J).comp S.symm.toContinuousLinearMap)

theorem centeredFrame_smooth {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (p : Phase n)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (centeredFrame S p u) :=
  S.contDiff.comp (hu.sub contDiff_const)

theorem centeredFrame_fderiv {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (p : Phase n)
    {u : ℂ → Phase n} (hu : Differentiable ℝ u) (z : ℂ) :
    fderiv ℝ (centeredFrame S p u) z=S.toContinuousLinearMap.comp (fderiv ℝ u z) := by
  exact (S.hasFDerivAt.comp z ((hu z).hasFDerivAt.sub_const p)).fderiv

theorem frozenCoefficient_smooth {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (J : End n)
    {B : ℂ → End n} (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (frozenCoefficient S J B) :=
  contDiff_const.clm_comp ((hB.sub contDiff_const).clm_comp contDiff_const)

theorem frozen_CR_equation {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (J : End n)
    (hS : ∀ v, S (J v)=Complex.I • S v) (p : Phase n)
    {u : ℂ → Phase n} (hu : Differentiable ℝ u) (B : ℂ → End n) {z : ℂ}
    (hCR : fderiv ℝ u z Complex.I=B z (fderiv ℝ u z 1)) :
    fderiv ℝ (centeredFrame S p u) z Complex.I-
      Complex.I • fderiv ℝ (centeredFrame S p u) z 1=
      frozenCoefficient S J B z (fderiv ℝ (centeredFrame S p u) z 1) := by
  rw [centeredFrame_fderiv S p hu z]
  change S (fderiv ℝ u z Complex.I)-Complex.I • S (fderiv ℝ u z 1)=
    S ((B z-J) (S.symm (S (fderiv ℝ u z 1))))
  simp only [S.symm_apply_apply,sub_apply,map_sub,hCR,hS]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
