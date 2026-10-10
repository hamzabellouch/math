import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealBeltrami
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

namespace OAI

/-! Quasiconformal change of variables for continuous Sobolev functions.

Oliva--Prats, *Sharp bounds for composition with quasiconformal mappings
in Sobolev spaces*, J. Math. Anal. Appl. 451 (2017), 1026--1044,
DOI 10.1016/j.jmaa.2017.02.016: Definition 2.1, Theorem 2.2 (null-set
preservation and inverse regularity), and Theorem 2.7, critical case
p = n = 2, with the chain rule in its proof;
https://arxiv.org/pdf/1612.00689, sections 2.1--2.2, pp. 4--7.

We assume only inverse weak derivatives, forward preservation of null
sets, and the scalar Sobolev chain rule for continuous compactly supported
functions. The squared Frobenius bound below is stronger than the operator
norm bound in Definition 2.1. No model or extremality assertion is assumed.
-/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def physicalHomeomorph (φ : ℂ ≃ₜ ℂ) : EuclideanPlane ≃ₜ EuclideanPlane :=
  (complexPlaneCoordinates.toHomeomorph.trans φ).trans
    complexPlaneCoordinates.toHomeomorph.symm

@[simp] theorem physicalHomeomorph_apply (φ : ℂ ≃ₜ ℂ) (x : EuclideanPlane) :
    physicalHomeomorph φ x = complexPlaneCoordinates.symm (φ (complexPlaneCoordinates x)) := rfl

@[simp] theorem physicalHomeomorph_symm (φ : ℂ ≃ₜ ℂ) :
    (physicalHomeomorph φ).symm = physicalHomeomorph φ.symm := rfl

 theorem planeSphere_physicalHomeomorph (φ : ℂ ≃ₜ ℂ) (x : EuclideanPlane) :
    planeSphere (physicalHomeomorph φ x) = φ.onePointCongr (planeSphere x) := by
  simp [planeSphere]

 def PlaneLocalWeakComplex.HasBoundedDistortion {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ᵐ x ∂volume,
    (D.realGradient x 0)^2 + (D.realGradient x 1)^2 +
      (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 ≤
        K * |D.realGradient x 0 * D.imagGradient x 1 -
          D.realGradient x 1 * D.imagGradient x 0|

 def PlaneQuasiconformalCalculus : Prop :=
  ∀ (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
    D.HasBoundedDistortion →
    ∃ E : PlaneLocalWeakComplex (fun x => φ.symm (complexPlaneCoordinates x)),
      Measure.QuasiMeasurePreserving (physicalHomeomorph φ.symm) volume volume ∧
      ∀ (u : EuclideanPlane → ℝ), Continuous u → HasCompactSupport u →
        ∀ H : DeGiorgi.MemW1pWitness 2 u univ,
        ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
          ∀ᵐ x ∂volume, ∀ j : Fin 2,
            V.weakGrad x j =
              H.weakGrad (physicalHomeomorph φ.symm x) 0 * E.realGradient x j +
              H.weakGrad (physicalHomeomorph φ.symm x) 1 * E.imagGradient x j

 theorem quasiconformal_compact_zero_gradient (hqc : PlaneQuasiconformalCalculus)
    (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ) (F : Set EuclideanPlane)
    (hz : ∀ j, ∀ᵐ x ∂volume, x ∈ F → H.weakGrad x j = 0) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
      ∀ j, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph φ '' F → V.weakGrad x j = 0 := by
  obtain ⟨E, hN, hcomp⟩ := hqc φ D hd
  obtain ⟨V, hV⟩ := hcomp u hu hs H
  refine ⟨V, fun j => ?_⟩
  filter_upwards [hV, hN.ae (hz 0), hN.ae (hz 1)] with x hx h0 h1 hxF
  have hin : physicalHomeomorph φ.symm x ∈ F := by
    obtain ⟨y, hy, rfl⟩ := hxF
    simpa only [← physicalHomeomorph_symm, Homeomorph.symm_apply_apply] using hy
  rw [hx j, h0 hin, h1 hin, zero_mul, zero_mul, add_zero]

end CircleDomainRigidity

end

end OAI
