import Mathlib
import OAI.Analysis.SymmetricDomains.AutFirstJetRegular
import OAI.Analysis.SymmetricDomains.ProjectedChartConjugationDifferential

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
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_conjugation_jacobian :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      ∀ g : Biholomorph U U,
      ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
          LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
        HasStrictFDerivAt (𝕜 := ℝ) (fun t => e (g*e.symm t*g⁻¹)) L (e 1) ∧
        Function.Bijective L ∧
        LinearMap.det (M := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)) L.toLinearMap =
          LinearMap.det (M := completeGeneratorSpace hU hc hbd Γ hhol) (generatorAdjoint hU hc hbd Γ hhol g).toLinearMap := by
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := J.range
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let k : completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] R :=
    LinearEquiv.ofInjective J (completeGeneratorFirstJet_injective hU hc hbd Γ hhol p)
  obtain ⟨P,e,he,he1,hP,_,hreg⟩ := exists_actual_aut_firstJet_regular_chart hU hc hbd Γ hhol p
  refine ⟨P,e,he,he1,?_⟩
  intro g
  obtain ⟨L,hL,hLX⟩ := projected_chart_conjugation_differential hU hc hbd Γ hhol p P e he he1 hreg g
  have hPk (X : completeGeneratorSpace hU hc hbd Γ hhol) : P (J X)=k X := by
    apply Subtype.ext
    exact hP X
  have hconj : L.toLinearMap=k.toLinearMap ∘ₗ
      (generatorAdjoint hU hc hbd Γ hhol g).toLinearMap ∘ₗ k.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨X,rfl⟩ := k.surjective v
    change L (k X)=k (generatorAdjoint hU hc hbd Γ hhol g (k.symm (k X)))
    rw [k.symm_apply_apply,← hPk X,← hPk]
    exact hLX X
  refine ⟨L,hL,?_,?_⟩
  · have heq : (L : R → R)=fun v => k (generatorAdjoint hU hc hbd Γ hhol g (k.symm v)) := by
      funext v
      exact LinearMap.congr_fun hconj v
    rw [heq]
    exact k.bijective.comp ((generatorAdjoint hU hc hbd Γ hhol g).bijective.comp k.symm.bijective)
  · rw [hconj]
    exact LinearMap.det_conj _ k
end Biholomorph
end Release061

end

end OAI
