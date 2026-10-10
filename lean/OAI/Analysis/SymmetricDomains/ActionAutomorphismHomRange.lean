import Mathlib
import OAI.Analysis.SymmetricDomains.DivisibleAutomorphismsSubsequence
import OAI.Analysis.SymmetricDomains.TendstoAmbientLocallyUniformly

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
open Set Filter Topology TopologicalSpace
open scoped Classical

instance Biholomorph.automorphismSecondCountable {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] : SecondCountableTopology (Biholomorph U U) :=
  Biholomorph.compactOpenPair_isEmbedding.secondCountableTopology

theorem bounded_divisible_automorphism_evaluation_proper {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsProperMap (fun a : Biholomorph U U => a.toHomeomorph p) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨Biholomorph.continuous_evaluation p,?_⟩
  intro K hK
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  obtain ⟨ρ,hρ,e,hf,hg⟩ := bounded_divisible_automorphisms_subsequence
    hU hc hb Γ hhol a p ⟨K,hK,Eventually.of_forall ha⟩
  have ht := Biholomorph.tendsto_of_ambient_locallyUniformly hf hg
  refine ⟨e,?_,ρ,hρ,ht⟩
  exact hK.isClosed.mem_of_tendsto ((Biholomorph.continuous_evaluation p).tendsto e |>.comp ht)
    (Eventually.of_forall fun j => ha (ρ j))

theorem bounded_divisible_automorphism_locallyCompact {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    LocallyCompactSpace (Biholomorph U U) := by
  have hp := bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p
  let : WeaklyLocallyCompactSpace (Biholomorph U U) := ⟨fun a => by
    obtain ⟨K,hK,hKa⟩ := exists_compact_mem_nhds (a.toHomeomorph p)
    exact ⟨_,hp.isCompact_preimage hK,hp.continuous.continuousAt.preimage_mem_nhds hKa⟩⟩
  infer_instance

noncomputable def actionAutomorphismHom {n : ℕ} (U : Set (Affine n))
    (Γ : Type*) [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    Γ →* Biholomorph U U where
  toFun := actionBiholomorph U Γ hhol
  map_one' := by apply Biholomorph.ext; intro x; exact one_smul Γ x
  map_mul' a b := by apply Biholomorph.ext; intro x; exact mul_smul a b x

theorem bounded_divisible_automorphism_compact_cover {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    ∃ K : Set (Biholomorph U U), IsCompact K ∧
      ∀ a : Biholomorph U U, ∃ γ : Γ, ∃ b ∈ K, a=actionAutomorphismHom U Γ hhol γ*b := by
  obtain ⟨K,hK,hcover⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  let H := actionAutomorphismHom U Γ hhol
  refine ⟨(fun a : Biholomorph U U => a.toHomeomorph p) ⁻¹' K,
    (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p).isCompact_preimage hK,?_⟩
  intro a
  obtain ⟨y,hy,γ,hγ⟩ := hcover (a.toHomeomorph p)
  refine ⟨γ,(H γ)⁻¹*a,?_,?_⟩
  · change γ⁻¹ • (a.toHomeomorph p) ∈ K
    rw [← hγ,inv_smul_smul]
    exact hy
  · change a=H γ*((H γ)⁻¹*a)
    group

theorem proper_discrete_orbit_map {X Γ : Type*} [TopologicalSpace X] [T2Space X]
    [CompactlyCoherentSpace X] [Group Γ] [TopologicalSpace Γ] [MulAction Γ X]
    [ProperSMul Γ X] (p : X) : IsProperMap (fun γ : Γ => γ • p) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_id.smul continuous_const,?_⟩
  intro K hK
  have h := (ProperSMul.isProperMap_smul_pair (G := Γ) (X := X)).isCompact_preimage
    (hK.prod (isCompact_singleton (x := p)))
  have he : Prod.fst '' ((fun gx : Γ × X => (gx.1 • gx.2,gx.2)) ⁻¹' (K ×ˢ {p})) =
      (fun γ : Γ => γ • p) ⁻¹' K := by
    ext γ
    constructor
    · rintro ⟨⟨δ,x⟩,⟨hx,hxp⟩,rfl⟩
      change δ • x ∈ K at hx
      change δ • p ∈ K
      rw [← mem_singleton_iff.mp hxp]
      exact hx
    · intro hγ
      exact ⟨(γ,p),⟨hγ,rfl⟩,rfl⟩
  rw [← he]
  exact h.image continuous_fst

theorem actionAutomorphismHom_proper {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsProperMap (actionAutomorphismHom U Γ hhol) := by
  exact isProperMap_of_comp_of_t2 continuous_of_discreteTopology
    (Biholomorph.continuous_evaluation p) (proper_discrete_orbit_map p)

theorem discrete_range_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology X] {f : X → Y} (hf : IsClosedMap f) : DiscreteTopology (Set.range f) := by
  apply discreteTopology_iff_forall_isClosed.mpr
  intro S
  have he : f '' (f ⁻¹' (Subtype.val '' S))=Subtype.val '' S := by
    apply image_preimage_eq_of_subset
    rintro x ⟨y,hy,rfl⟩
    exact y.property
  have h := (hf _ (isClosed_discrete (f ⁻¹' (Subtype.val '' S)))).preimage
    (continuous_subtype_val (p := fun x => x ∈ Set.range f))
  rw [he,preimage_image_eq _ Subtype.val_injective] at h
  exact h

theorem actionAutomorphismHom_range_discrete {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsClosed ((actionAutomorphismHom U Γ hhol).range : Set (Biholomorph U U)) ∧
      DiscreteTopology (actionAutomorphismHom U Γ hhol).range := by
  have hp := actionAutomorphismHom_proper Γ hhol p
  exact ⟨hp.isClosedMap.isClosed_range,discrete_range_of_isClosedMap hp.isClosedMap⟩

end Release061

end

end OAI
