import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectedChartConjugationDifferential
import OAI.Analysis.SymmetricDomains.AutChartUnimodularJacobian

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
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem generatorAdjoint_abs_det_one (g : Biholomorph U U) :
    |(generatorAdjoint hU hc hbd Γ hhol g).toLinearMap.det|=1 := by
  obtain ⟨p,hp⟩ := hc.nonempty
  let p : U := ⟨p,hp⟩
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := J.range
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨P,e,he,he1,hP,hreg,hdet⟩ := exists_actual_aut_chart_unimodular_jacobian hU hc hbd Γ hhol p
  have hreg' (p' : U) : ∃ L : R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p' (e.symm t)) L (e 1) :=
    ⟨_,(hreg p' (e 1) (e.map_source he1)).hasStrictFDerivAt (by simp)⟩
  obtain ⟨L,hL,hLX⟩ := projected_chart_conjugation_differential hU hc hbd Γ hhol p
    P e he he1 hreg' g
  let j : completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] R :=
    LinearEquiv.ofInjective J (completeGeneratorFirstJet_injective hU hc hbd Γ hhol p)
  have hj (X : completeGeneratorSpace hU hc hbd Γ hhol) : P (J X)=j X := by
    apply Subtype.ext
    exact hP X
  have hconj : L.toLinearMap=j.toLinearMap ∘ₗ
      (generatorAdjoint hU hc hbd Γ hhol g).toLinearMap ∘ₗ j.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨X,rfl⟩ := j.surjective v
    change L (j X)=j (generatorAdjoint hU hc hbd Γ hhol g (j.symm (j X)))
    rw [j.symm_apply_apply,←hj,←hj]
    exact hLX X
  have hd : L.det=(generatorAdjoint hU hc hbd Γ hhol g).toLinearMap.det := by
    change L.toLinearMap.det=_
    rw [hconj,LinearMap.det_conj]
  rw [←hd,←hL.hasFDerivAt.fderiv]
  exact hdet g

theorem completeGenerator_trace_ad_eq_zero
    (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    LinearMap.trace ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
      (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol) X)=0 := by
  classical
  let _ : FiniteDimensional ℝ (completeGeneratorSpace hU hc hbd Γ hhol) :=
    finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  let b := Module.finBasis ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
  obtain ⟨a,ha,ha0,ham,hgen⟩ := X.property
  have hg : oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham=X := by
    apply Subtype.ext
    exact hgen
  have hdet (t : ℝ) : generatorDeterminant hU hc hbd Γ hhol b (a t)=1 := by
    have hh := generatorAdjoint_abs_det_one hU hc hbd Γ hhol (a t)
    have he : generatorDeterminant hU hc hbd Γ hhol b (a t)=
        (generatorAdjoint hU hc hbd Γ hhol (a t)).toLinearMap.det := by
      exact LinearMap.det_toMatrix b _
    rw [←he,abs_of_pos (generatorDeterminant_flow_pos hU hc hbd Γ hhol b a ham t)] at hh
    exact hh
  have hd := generatorDeterminant_hasDerivAt_zero hU hc hbd Γ hhol b a ha ha0 ham
  rw [hg] at hd
  have hzero := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hdet))
  exact neg_eq_zero.mp hzero
end Biholomorph
end Release061

end

end OAI
