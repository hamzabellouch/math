import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectedJetSequencesNot

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
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU hc hbd Γ hhol

theorem projected_firstJet_locally_injective
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (hP : ∀ X : Affine n → Affine n, IsCompleteGenerator U X →
      P (X p.val,fderiv ℂ X p.val)=0 → X=0) :
    ∃ W : Set (Biholomorph U U), W∈𝓝 1 ∧ Set.InjOn (fun a => P (ambientFirstJet p a)) W := by
  classical
  by_contra hn
  let W : ℕ → Set (Biholomorph U U) := fun i =>
    firstJet p ⁻¹' ball (firstJet p 1) (1/((i:ℝ)+1))
  have hW (i : ℕ) : W i∈𝓝 1 := (firstJet_continuous hU p).continuousAt.preimage_mem_nhds
    (ball_mem_nhds _ (by positivity))
  have hex (i : ℕ) : ∃ a∈W i, ∃ b∈W i,
      P (ambientFirstJet p a)=P (ambientFirstJet p b) ∧ a≠b := by
    have hi : ¬Set.InjOn (fun a => P (ambientFirstJet p a)) (W i) := fun hi => hn ⟨W i,hW i,hi⟩
    unfold Set.InjOn at hi
    push Not at hi
    exact hi
  choose a ha b hb he hne using hex
  have hv (q : ℕ → Biholomorph U U) (hq : ∀ i, q i∈W i) : Tendsto q atTop (𝓝 1) := by
    apply (firstJet_isClosedEmbedding hU hc hbd Γ hhol p).isEmbedding.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun i => (hq i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  exact projected_jet_sequences_not_coincident hU hc hbd Γ hhol p P hP a b (hv a ha) (hv b hb) hne he

omit hc in

theorem exists_complete_generator_jet_projection (hc' : IsConnected U) :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc' hbd Γ hhol p),
      (∀ X : completeGeneratorSpace hU hc' hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc' hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc' hbd Γ hhol p X) ∧
      (∀ X : Affine n → Affine n, IsCompleteGenerator U X →
        P (X p.val,fderiv ℂ X p.val)=0 → X=0) := by
  classical
  let J := completeGeneratorFirstJet hU hc' hbd Γ hhol p
  obtain ⟨K,hK⟩ := (LinearMap.range J).exists_isCompl
  let P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] LinearMap.range J :=
    ⟨(LinearMap.range J).projectionOnto K hK,
      LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := Affine n × (Affine n →L[ℂ] Affine n))
        (F' := LinearMap.range J) ((LinearMap.range J).projectionOnto K hK)⟩
  refine ⟨P,?_,?_⟩
  · intro X
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_of_mem_left hK ⟨X,rfl⟩)
  · intro X hX hz
    have hJ : J ⟨X,hX⟩=0 := by
      have he := Submodule.projectionOnto_apply_of_mem_left hK (show J ⟨X,hX⟩∈LinearMap.range J from ⟨⟨X,hX⟩,rfl⟩)
      have hp : P (J ⟨X,hX⟩)=0 := hz
      have hpv := congrArg Subtype.val hp
      change ((J.range.projectionOnto K hK) (J ⟨X,hX⟩)).val=0 at hpv
      rw [he] at hpv
      exact hpv
    have hx0 : (⟨X,hX⟩ : completeGeneratorSpace hU hc' hbd Γ hhol)=0 :=
      (completeGeneratorFirstJet_injective hU hc' hbd Γ hhol p) (by simpa only [map_zero] using hJ)
    exact congrArg Subtype.val hx0
end Biholomorph
end Release061

end

end OAI
