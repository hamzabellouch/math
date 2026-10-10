import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.WeightedPrincipal

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [Fintype ι] in
lemma weightedPrincipal_contDiffAt (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ)
    {x : V} (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hρ : ContDiffAt ℝ ∞ ρ x) (i j : ι) :
    ContDiffAt ℝ ∞ (weightedPrincipal a ρ i j) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact ((S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j))

lemma actualSquareFirst_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (actualSquareFirst e a b ρ j) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hsum : ContDiffAt ℝ ∞ (fun z => ∑ i, fderiv ℝ (weightedPrincipal a ρ i j) z (e i)) x :=
    ContDiffAt.sum fun i _ => ((weightedPrincipal_contDiffAt a ρ ha hρ i j).fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

def weightedLower (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (i : ι) (x : V) : End (W := W) := (ρ x • a i x).adjoint ∘L b x

def actualSquareZero (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (x : V) : End (W := W) :=
  -(ρ x)⁻¹ • (∑ i, fderiv ℝ (weightedLower a b ρ i) x (e i)) + (b x).adjoint ∘L b x

lemma actualSquareZero_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (actualSquareZero e a b ρ) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hw (i : ι) : ContDiffAt ℝ ∞ (weightedLower a b ρ i) x :=
    ((S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp hb)
  have hsum : ContDiffAt ℝ ∞ (fun z => ∑ i, fderiv ℝ (weightedLower a b ρ i) z (e i)) x :=
    ContDiffAt.sum fun i _ => ((hw i).fderiv_right (by simp)).clm_apply contDiffAt_const
  exact ((hρ.inv hρx).neg.smul hsum).add ((S.contDiff.contDiffAt.comp x hb).clm_comp hb)

lemma transformedFirst_contDiffAt (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (U : V → End (W := W)) (e : ι → V) (j : ι) {x : V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hU : ContDiffAt ℝ ∞ U x) : ContDiffAt ℝ ∞ (transformedFirst a b U e j) x := by
  have hDU : ContDiffAt ℝ ∞ (fderiv ℝ U) x := hU.fderiv_right (by simp)
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hb j).clm_comp hU).sub (ContDiffAt.sum fun i _ =>
      ((ha i j).add (ha j i)).smul (hDU.clm_apply contDiffAt_const)))

def transformedZero (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (c U : V → End (W := W)) (e : ι → V) (x : V) : End (W := W) :=
  (U x).adjoint ∘L (c x ∘L U x + (∑ i, b i x ∘L fderiv ℝ U x (e i)) -
    ∑ i, ∑ j, a i j x • fderiv ℝ (fun z => fderiv ℝ U z (e j)) x (e i))

lemma transformedZero_contDiffAt (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (c U : V → End (W := W)) (e : ι → V) {x : V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) (hU : ContDiffAt ℝ ∞ U x) :
    ContDiffAt ℝ ∞ (transformedZero a b c U e) x := by
  have hDU : ContDiffAt ℝ ∞ (fderiv ℝ U) x := hU.fderiv_right (by simp)
  have hDDU (i j : ι) : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun z => fderiv ℝ U z (e j)) z (e i)) x :=
    ((hDU.clm_apply contDiffAt_const).fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hc.clm_comp hU).add (ContDiffAt.sum fun i _ =>
      (hb i).clm_comp (hDU.clm_apply contDiffAt_const))).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (ha i j).smul (hDDU i j)))

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
