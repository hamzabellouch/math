import Mathlib
import OAI.Analysis.SymmetricDomains.QuadraticModelResidualFiber
import OAI.Analysis.SymmetricDomains.IsotropyRepresentationUnitsCompact
import OAI.Analysis.SymmetricDomains.ModelAxisNegativeIsotropy

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
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph

theorem hermitian_model_to_axis {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (p : (affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) :
    ∃ b : Biholomorph
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C),
      ∃ a : Fin k → ℝ, (b.toHomeomorph p).val=Complex.I • flatNormalVector r k a := by
  let L := affineProductCoordinates r k
  let D := quadraticDomain (Hermitian.hermQuadratic B) C
  let S := L '' D
  let q := L.symm p.val
  let a := Hermitian.axisNormalization B q
  let f := (L.toHomeomorph.symm.trans a).trans L.toHomeomorph
  have hf : AnalyticOnNhd ℂ f univ := by
    intro x _
    exact (L.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.axisNormalization_analytic B q _ (mem_univ _)).comp
        (L.symm.toContinuousLinearMap.analyticAt x))
  have hfi : AnalyticOnNhd ℂ f.symm univ := by
    intro x _
    exact (L.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.axisNormalization_inverse_analytic B q _ (mem_univ _)).comp
        (L.symm.toContinuousLinearMap.analyticAt x))
  have hm : MapsTo f S S := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨a x,(Hermitian.axisNormalization_mem B C q x).mpr hx,?_⟩
    simp [f]
  have hmi : MapsTo f.symm S S := by
    rintro _ ⟨x,hx,rfl⟩
    have hi : a.symm x∈D := (Hermitian.axisNormalization_mem B C q (a.symm x)).mp
      (by simpa only [a,a.apply_symm_apply] using hx)
    refine ⟨a.symm x,hi,?_⟩
    simp [f]
  let b := biholomorphOfAmbientInverse S S f f.symm (hf.mono (subset_univ _))
    (hfi.mono (subset_univ _)) hm hmi (fun x _ => f.symm_apply_apply x)
    (fun x _ => f.apply_symm_apply x)
  refine ⟨b,fun i => (q.2 i).im-Hermitian.hermQuadratic B q.1 i,?_⟩
  change L (a q)=_
  rw [Hermitian.axisNormalization_apply]
  rw [flatNormalVector,←map_smul]
  congr 1
  ext i <;> simp

variable {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

include hU hc hbd Γ hhol in

theorem hermitian_model_bounded_symmetric {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hDo : IsOpen (quadraticDomain (Hermitian.hermQuadratic B) C))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (Hermitian.hermQuadratic B) C ↔
        p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈
      quadraticDomain (Hermitian.hermQuadratic B) C ↔ p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈quadraticDomain (Hermitian.hermQuadratic B) C ↔
      p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)]
    (e : Biholomorph ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) U) :
    IsBoundedSymmetricDomain U := by
  apply (boundedSymmetricDomain_iff_negative_isotropy hU hc hbd).mpr
  intro p
  let q := e.toHomeomorph.symm p
  obtain ⟨b,a,ha⟩ := hermitian_model_to_axis B C q
  let e' := b.symm.trans e
  let q' := b.toHomeomorph q
  have hep : e'.toHomeomorph q'=p := by
    change e.toHomeomorph (b.toHomeomorph.symm (b.toHomeomorph (e.toHomeomorph.symm p)))=p
    simp only [b.toHomeomorph.symm_apply_apply,e.toHomeomorph.apply_symm_apply]
  obtain ⟨s,hs,hd'⟩ := model_axis_negative_isotropy hU hc hbd Γ hhol
    (quadraticDomain (Hermitian.hermQuadratic B) C) hDo htr hd hr e' q' a ha
  rw [hep] at hs hd'
  exact ⟨s,hs,hd'⟩

end Biholomorph
end Release061

end

end OAI
