import Mathlib
import OAI.Analysis.SymmetricDomains.CompleteGeneratorJetProjection
import OAI.Analysis.SymmetricDomains.ProjectedChartObservableStrict
import OAI.Analysis.SymmetricDomains.FiniteFlowParametrization

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
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_firstJet_chart :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : CompleteSpace R := FiniteDimensional.complete ℝ R
  obtain ⟨P,hP,hPinj⟩ := exists_complete_generator_jet_projection hU hbd Γ hhol p hc
  obtain ⟨W,hW,hinj⟩ := projected_firstJet_locally_injective (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)) hU hc.isPreconnected hbd Γ hhol p P hPinj
  obtain ⟨F,hF,hF0,hd⟩ := exists_finite_flow_parametrization hU hc hbd Γ hhol p P hP
  obtain ⟨e,he,he1⟩ := openChart_of_projected_parametrization (A := Biholomorph U U) (E := R)
    (fun a => P (ambientFirstJet p a)) (P.continuous.comp (ambientFirstJet_continuous hU p))
    1 W hW hinj F hF hF0 hd
  exact ⟨P,e,he,he1,hP⟩

theorem exists_actual_aut_firstJet_regular_chart :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
        (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p (e.symm t))
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)).subtypeL (e 1) ∧
      ∀ p' : U, ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
          (Affine n × (Affine n →L[ℂ] Affine n)),
        HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
          (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p' (e.symm t)) L (e 1) := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : CompleteSpace R := FiniteDimensional.complete ℝ R
  obtain ⟨P,hP,hPinj⟩ := exists_complete_generator_jet_projection hU hbd Γ hhol p hc
  obtain ⟨W,hW,hinj⟩ := projected_firstJet_locally_injective (E := R)
    hU hc.isPreconnected hbd Γ hhol p P hPinj
  obtain ⟨F,hF,hF0,hd,hjet,hreg⟩ := exists_finite_flow_parametrization_with_regular_jets hU hc hbd Γ hhol p P hP
  obtain ⟨e,he,he1⟩ := openChart_of_projected_parametrization (A := Biholomorph U U) (E := R)
    (fun a => P (ambientFirstJet p a)) (P.continuous.comp (ambientFirstJet_continuous hU p))
    1 W hW hinj F hF hF0 hd
  refine ⟨P,e,he,he1,hP,?_,?_⟩
  · apply projected_chart_observable_hasStrictFDerivAt (E := R) e 1 he1 F hF hF0 _
      (ambientFirstJet p) _ hjet
    simpa only [he] using hd
  · intro p'
    obtain ⟨L,hL⟩ := hreg p' 0
    refine ⟨L,?_⟩
    apply projected_chart_observable_hasStrictFDerivAt (E := R) e 1 he1 F hF hF0 _
      (ambientFirstJet p') L hL
    simpa only [he] using hd

end Biholomorph
end Release061

end

end OAI
