import Mathlib
import OAI.Analysis.SymmetricDomains.QuadraticModelResidualFiber
import OAI.Analysis.SymmetricDomains.ScalarTubeInvolution

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def scalarNormalCoordinates : (E × (Fin 1 → ℂ)) ≃L[ℂ] (E × ℂ) :=
  (ContinuousLinearEquiv.refl ℂ E).prodCongr (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
@[simp] lemma scalarNormalCoordinates_apply (p : E × (Fin 1 → ℂ)) :
    scalarNormalCoordinates p = (p.1,p.2 0) := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
@[simp] lemma scalarNormalCoordinates_symm_apply (p : E × ℂ) :
    scalarNormalCoordinates.symm p = (p.1,fun _ : Fin 1 => p.2) := rfl

omit [FiniteDimensional ℂ E] in
lemma scalar_hermQuadratic_homogeneous
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (z : E) :
    hermQuadratic B (c • z) 0 = normSq c * hermQuadratic B z 0 := by
  change (hermPart (symmetrize (B 0)) (c • z) (c • z)).re = _
  rw [hermPart_smul_both]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  rfl

omit [FiniteDimensional ℂ E] [IsScalarTower ℝ ℂ E] in
lemma scalarNormalCoordinates_mem
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin 1 → ℂ)) :
    scalarNormalCoordinates p ∈ scalarTube (fun z => hermQuadratic B z 0) ↔
    p ∈ quadraticDomain (hermQuadratic B) {a | 0 < a 0} := by
  change hermQuadratic B p.1 0 < (p.2 0).im ↔ 0 < (p.2 0).im-hermQuadratic B p.1 0
  exact sub_pos.symm

def scalarAxisNormalization
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × ℂ) : (E × ℂ) ≃ₜ (E × ℂ) :=
  scalarNormalCoordinates.symm.toHomeomorph.trans
    ((axisNormalization B (scalarNormalCoordinates.symm p)).trans
      scalarNormalCoordinates.toHomeomorph)

lemma scalarAxisNormalization_apply
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × ℂ) :
    scalarAxisNormalization B p p = (0,I*((p.2.im-hermQuadratic B p.1 0 : ℝ) : ℂ)) := by
  change scalarNormalCoordinates (axisNormalization B (scalarNormalCoordinates.symm p)
    (scalarNormalCoordinates.symm p)) = _
  rw [axisNormalization_apply]
  rfl

lemma scalarAxisNormalization_mem
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p q : E × ℂ) :
    scalarAxisNormalization B p q ∈ scalarTube (fun z => hermQuadratic B z 0) ↔
      q ∈ scalarTube (fun z => hermQuadratic B z 0) := by
  change scalarNormalCoordinates (axisNormalization B _ _) ∈ _ ↔ _
  rw [scalarNormalCoordinates_mem,axisNormalization_mem]
  exact (scalarNormalCoordinates_mem B (scalarNormalCoordinates.symm q)).symm.trans
    (by rw [ContinuousLinearEquiv.apply_symm_apply])

lemma scalarAxisNormalization_analytic
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × ℂ) :
    AnalyticOnNhd ℂ (scalarAxisNormalization B p) univ := by
  intro q _
  exact (scalarNormalCoordinates.analyticAt _).comp
    ((axisNormalization_analytic B _ _ (mem_univ _)).comp
      (scalarNormalCoordinates.symm.analyticAt q))

lemma scalarAxisNormalization_inverse_analytic
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × ℂ) :
    AnalyticOnNhd ℂ (scalarAxisNormalization B p).symm univ := by
  intro q _
  exact (scalarNormalCoordinates.analyticAt _).comp
    ((axisNormalization_inverse_analytic B _ _ (mem_univ _)).comp
      (scalarNormalCoordinates.symm.analyticAt q))

def scalarPointSymmetryMap
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p q : E × ℂ) : E × ℂ :=
  (scalarAxisNormalization B p).symm
    (scalarNormalInversion (p.2.im-hermQuadratic B p.1 0) (scalarAxisNormalization B p q))

lemma scalarPointSymmetryMap_mem
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ z, 0 ≤ hermQuadratic B z 0)
    {p q : E × ℂ} (hp : p ∈ scalarTube (fun z => hermQuadratic B z 0))
    (hq : q ∈ scalarTube (fun z => hermQuadratic B z 0)) :
    scalarPointSymmetryMap B p q ∈ scalarTube (fun z => hermQuadratic B z 0) := by
  have hy : 0 < p.2.im-hermQuadratic B p.1 0 := sub_pos.mpr hp
  have hm := scalarNormalInversion_mem (scalar_hermQuadratic_homogeneous B) hB hy.ne'
    ((scalarAxisNormalization_mem B p q).mpr hq)
  apply (scalarAxisNormalization_mem B p _).mp
  change scalarAxisNormalization B p ((scalarAxisNormalization B p).symm _) ∈ _
  rw [Homeomorph.apply_symm_apply]
  exact hm

lemma scalarPointSymmetryMap_involutive
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ z, 0 ≤ hermQuadratic B z 0)
    {p q : E × ℂ} (hp : p ∈ scalarTube (fun z => hermQuadratic B z 0))
    (hq : q ∈ scalarTube (fun z => hermQuadratic B z 0)) :
    scalarPointSymmetryMap B p (scalarPointSymmetryMap B p q) = q := by
  have hy : 0 < p.2.im-hermQuadratic B p.1 0 := sub_pos.mpr hp
  simp only [scalarPointSymmetryMap,Homeomorph.apply_symm_apply]
  rw [scalarNormalInversion_involutive hy.ne' _
    (scalarTube_normal_ne_zero hB ((scalarAxisNormalization_mem B p q).mpr hq)),
    Homeomorph.symm_apply_apply]

lemma scalarPointSymmetryMap_analytic
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ z, 0 ≤ hermQuadratic B z 0)
    (p : E × ℂ) : AnalyticOnNhd ℂ (scalarPointSymmetryMap B p)
      (scalarTube (fun z => hermQuadratic B z 0)) := by
  intro q hq
  exact (scalarAxisNormalization_inverse_analytic B p _ (mem_univ _)).comp
    ((scalarNormalInversion_analytic _
      (scalarTube_normal_ne_zero hB ((scalarAxisNormalization_mem B p q).mpr hq))).comp
        (scalarAxisNormalization_analytic B p q (mem_univ _)))

lemma scalarPointSymmetryMap_fixed_iff
    (B : Fin 1 → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ z, 0 ≤ hermQuadratic B z 0)
    {p q : E × ℂ} (hp : p ∈ scalarTube (fun z => hermQuadratic B z 0))
    (hq : q ∈ scalarTube (fun z => hermQuadratic B z 0)) :
    scalarPointSymmetryMap B p q = q ↔ q = p := by
  have hy : 0 < p.2.im-hermQuadratic B p.1 0 := sub_pos.mpr hp
  change (scalarAxisNormalization B p).symm _ = q ↔ q = p
  rw [Homeomorph.symm_apply_eq]
  rw [scalarNormalInversion_fixed_iff hB hy ((scalarAxisNormalization_mem B p q).mpr hq)]
  rw [← scalarAxisNormalization_apply B p]
  exact (scalarAxisNormalization B p).injective.eq_iff

end Release061.Hermitian

end

end OAI
