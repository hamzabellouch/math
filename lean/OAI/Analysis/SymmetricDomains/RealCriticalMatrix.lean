import Mathlib
import OAI.Analysis.SymmetricDomains.AffineBand

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
namespace Release061
open Set Filter Topology
open scoped Classical

noncomputable def realCriticalMatrix {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) (x : Fin d → ℝ) :
    ((Fin N → ℂ) →L[ℂ] ℂ) →L[ℝ] (Fin d → ℝ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip (fderiv ℝ q x)).comp
      (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)).symm.toContinuousLinearMap)

noncomputable def realCriticalConstant {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ := -(ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)) (fderiv ℝ f x)

lemma realCriticalMatrix_apply {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    (x : Fin d → ℝ) (a : (Fin N → ℂ) →L[ℂ] ℂ) :
    realCriticalMatrix q x a =
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d))
        ((Complex.reCLM.comp (a.restrictScalars ℝ)).comp (fderiv ℝ q x)) := rfl

lemma realCriticalMatrix_surjective {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    {x : Fin d → ℝ} (hq : Function.Injective (fderiv ℝ q x)) :
    Function.Surjective (realCriticalMatrix q x) := by
  let v := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)
  intro t
  obtain ⟨l,hl⟩ := LinearMap.dualMap_surjective_of_injective hq (v.symm t).toLinearMap
  let l' : (Fin N → ℂ) →L[ℝ] ℝ := l.toContinuousLinearMap
  refine ⟨(StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)) l',?_⟩
  change v (((ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip (fderiv ℝ q x))
    ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)).symm
      ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)) l'))) = t
  rw [ContinuousLinearEquiv.symm_apply_apply]
  change v (l'.comp (fderiv ℝ q x)) = t
  have he : l'.comp (fderiv ℝ q x) = v.symm t := by
    apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun L : (Fin d → ℝ) →ₗ[ℝ] ℝ => L z) hl
  rw [he,v.apply_symm_apply]

lemma realCriticalMatrix_contDiffAt {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    {x : Fin d → ℝ} (hq : ContDiffAt ℝ 2 q x) :
    ContDiffAt ℝ 1 (realCriticalMatrix q) x := by
  have hq' : ContDiffAt ℝ 1 (fderiv ℝ q) x := hq.fderiv_right (by norm_num)
  let L := (ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip
  have hL0 : ContDiff ℝ 1 (fun v : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) := by
    apply ContinuousLinearMap.contDiff
  have hL : ContDiffAt ℝ 1 (fun y => L (fderiv ℝ q y)) x :=
    hL0.contDiffAt.comp x hq'
  exact contDiffAt_const.clm_comp (hL.clm_comp contDiffAt_const)

lemma realCriticalConstant_contDiffAt {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (realCriticalConstant f) x := by
  exact (((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).contDiff.contDiffAt).comp x
    (hf.fderiv_right (by norm_num))).neg

theorem realCriticalMatrix_eq_iff {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hq : DifferentiableAt ℝ q x) (hf : DifferentiableAt ℝ f x)
    (a : (Fin N → ℂ) →L[ℂ] ℂ) :
    realCriticalMatrix q x a = realCriticalConstant f x ↔
      fderiv ℝ (fun y => f y + (a (q y)).re) x = 0 := by
  have hd : HasFDerivAt (fun y => f y + (a (q y)).re)
      (fderiv ℝ f x + (Complex.reCLM.comp (a.restrictScalars ℝ)).comp (fderiv ℝ q x)) x :=
    hf.hasFDerivAt.add (((Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt)
  rw [hd.fderiv,realCriticalMatrix_apply,realCriticalConstant,← map_neg,
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).injective.eq_iff]
  exact eq_neg_iff_add_eq_zero.trans (by rw [add_comm])

end Release061

end

end OAI
