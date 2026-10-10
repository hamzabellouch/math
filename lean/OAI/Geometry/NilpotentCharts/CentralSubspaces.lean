import Mathlib
import OAI.Geometry.NilpotentCharts.CentralWords
import OAI.Geometry.NilpotentCharts.RationalCoordinates

namespace OAI

/-! Closed central subspaces and rationality of the final lower-central layer. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
variable (K : Submodule ℝ E₀) (hKC : K ≤ RawLieAdjoint.centralTangent (G := G) (E₀ := E₀))
include hKC

lemma subspaceAxes_central_inclusion (z : K) :
    subspaceAxes (G := G) K z = subspaceAxes (G := G) (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) (K.inclusion hKC z) := by
  let b := Module.finBasis ℝ K
  let f := K.inclusion hKC
  have H := centralAxes_sum (G := G) (List.ofFn (fun i => b.equivFun z i • f (b i)))
  simp only [List.sum_ofFn,List.map_ofFn] at H
  have hs : (∑ i, b.equivFun z i • f (b i)) = f z := by
    simp only [← map_smul,← map_sum,b.sum_equivFun]
  rw [hs] at H
  rw [H]
  change (List.ofFn (fun i => curve (G := G) (b i).val (b.equivFun z i))).prod = _
  congr 2
  funext i
  exact (centralAxes_smul (f (b i)) (b.equivFun z i)).symm

def centralSubspaceHom (K : Submodule ℝ E₀)
    (hKC : K ≤ RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) : Multiplicative K →* G :=
  (centralAxesHom (G := G) (E₀ := E₀)).comp (K.inclusion hKC).toAddMonoidHom.toMultiplicative

lemma centralSubspaceHom_apply (z : K) :
    centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd z) = subspaceAxes (G := G) K z :=
  (subspaceAxes_central_inclusion (G := G) K hKC z).symm

lemma centralSubspaceHom_le_center : (centralSubspaceHom (G := G) K hKC).range ≤ Subgroup.center G := by
  rintro g ⟨v,rfl⟩
  exact centralAxesHom_range_le_center (G := G) (E₀ := E₀) ⟨_,rfl⟩

lemma centralSubspaceAxes_closedEmbedding [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Topology.IsClosedEmbedding (subspaceAxes (G := G) K) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : SimplyConnectedSpace (centralAxesHom (G := G) (E₀ := E₀)).range :=
    central_range_simplyConnected_of_nilpotent hstop
  have hc : Topology.IsClosedEmbedding (subspaceAxes (G := G) (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀))) :=
    (centralAxesHom_range_isClosed (G := G) (E₀ := E₀)).isClosedEmbedding_subtypeVal.comp
    (centralHomeomorph (G := G)).isClosedEmbedding
  have hf := (K.inclusion hKC).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective hKC))
  have he : subspaceAxes (G := G) K =
      subspaceAxes (G := G) (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) ∘ K.inclusion hKC :=
    funext (subspaceAxes_central_inclusion (G := G) K hKC)
  have H : Topology.IsClosedEmbedding (subspaceAxes (G := G) (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) ∘ K.inclusion hKC) := hc.comp hf
  exact he.symm ▸ H

lemma centralSubspace_range_membership (g : G) :
    g ∈ (centralSubspaceHom (G := G) K hKC).range ↔ ∃ z : K, subspaceAxes (G := G) K z = g := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v.toAdd,(centralSubspaceHom_apply (G := G) K hKC _).symm.trans hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨Multiplicative.ofAdd v,(centralSubspaceHom_apply (G := G) K hKC _).trans hv⟩

lemma centralSubspace_range_closed [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    IsClosed ((centralSubspaceHom (G := G) K hKC).range : Set G) := by
  have he : ((centralSubspaceHom (G := G) K hKC).range : Set G) = Set.range (subspaceAxes K) :=
    Set.ext (centralSubspace_range_membership (G := G) K hKC)
  rw [he]
  exact (centralSubspaceAxes_closedEmbedding (G := G) K hKC hstop).isClosed_range

instance centralSubspace_range_normal : ((centralSubspaceHom (G := G) K hKC).range).Normal where
  conj_mem a ha b := by
    have hc := Subgroup.mem_center_iff.mp (centralSubspaceHom_le_center (G := G) K hKC ha) b
    simpa only [hc,mul_inv_cancel_right] using ha

end RawLieIntegration

namespace RawLieIntegration
open RawCentralWords
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
open scoped commutatorElement

omit [TopologicalSpace G] [T2Space G] in
lemma last_lowerCentral_le_center {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries (s+1) = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries s ≤ Subgroup.center G := by
  intro g hg
  apply Subgroup.mem_center_iff.mpr
  intro x
  have H : ⁅g,x⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (s+1) :=
    Subgroup.commutator_mem_commutator hg (Subgroup.mem_top x)
  rw [hstop,Subgroup.mem_bot] at H
  exact (commutatorElement_eq_one_iff_mul_comm.mp H).symm

include E₀ in
 

theorem last_central_rational_subspace [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries (s+1) = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (K : Submodule ℝ E₀) (hKC : K ≤ (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀))),
      (centralSubspaceHom (G := G) K hKC).range =
        @Subgroup.topologicalClosure G _ _ (topologicalGroup_of_lieGroup I₀ ∞) ((⊤ : Subgroup G).lowerCentralSeries s) ∧
      Submodule.span ℝ {v : K | subspaceAxes (G := G) K v ∈ Γ} = ⊤ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : SimplyConnectedSpace (centralAxesHom (G := G) (E₀ := E₀)).range :=
    central_range_simplyConnected_of_nilpotent hstop
  obtain ⟨n,c,_,hΓ,L,hL⟩ := centric_rational_coordinates (E₀ := E₀) hstop Γ
  let φ := centralAxesHom (G := G) (E₀ := E₀)
  have hφ : Topology.IsClosedEmbedding (fun v : (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) => φ (Multiplicative.ofAdd v)) :=
    (centralAxesHom_range_isClosed (G := G) (E₀ := E₀)).isClosedEmbedding_subtypeVal.comp
      (centralHomeomorph (G := G)).isClosedEmbedding
  let Kc := centralWordSpan c L s
  have hc := centralWordSpan_closure c L φ (Subgroup.center G) s
    (last_lowerCentral_le_center hstop) hL hφ
  have hl := centralWordSpan_lattice_span c L φ (Subgroup.center G) s
    (last_lowerCentral_le_center hstop) hL Γ hΓ
  let K := Kc.map (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)).subtype
  have hKC : K ≤ (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) := by
    rintro x ⟨z,hz,rfl⟩
    exact z.property
  refine ⟨K,hKC,?_,?_⟩
  · rw [← hc]
    ext g
    constructor
    · rintro ⟨v,hv⟩
      obtain ⟨z,hz,hzv⟩ := v.toAdd.property
      refine ⟨Multiplicative.ofAdd z,hz,?_⟩
      rw [← hv]
      change subspaceAxes (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) z = subspaceAxes (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) (K.inclusion hKC v.toAdd)
      congr 1
      exact Subtype.ext hzv
    · rintro ⟨v,hv,hvg⟩
      exact ⟨Multiplicative.ofAdd ⟨v.toAdd.val,Submodule.mem_map_of_mem hv⟩,hvg⟩
  · let T := K.inclusion hKC
    have hTin : Injective T := Submodule.inclusion_injective hKC
    have hr : LinearMap.range T = Kc := by
      ext z
      constructor
      · rintro ⟨v,rfl⟩
        obtain ⟨x,hx,hxv⟩ := v.property
        have he : x = T v := Subtype.ext hxv
        exact he ▸ hx
      · intro hz
        exact ⟨⟨z.val,Submodule.mem_map_of_mem hz⟩,rfl⟩
    have him : T '' {v : K | subspaceAxes (G := G) K v ∈ Γ} =
        {v : (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) | v ∈ Kc ∧ φ (Multiplicative.ofAdd v) ∈ Γ} := by
      ext z
      constructor
      · rintro ⟨v,hv,rfl⟩
        refine ⟨hr ▸ (show T v ∈ LinearMap.range T from ⟨v,rfl⟩),?_⟩
        change subspaceAxes (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)) (T v) ∈ Γ
        rw [← subspaceAxes_central_inclusion (G := G) K hKC]
        exact hv
      · rintro ⟨hz,hzΓ⟩
        let v : K := ⟨z.val,Submodule.mem_map_of_mem hz⟩
        refine ⟨v,?_,rfl⟩
        change subspaceAxes (G := G) K v ∈ Γ
        rw [subspaceAxes_central_inclusion (G := G) K hKC]
        exact hzΓ
    apply Submodule.map_injective_of_injective hTin
    rw [Submodule.map_span,him,Submodule.map_top,hr]
    exact hl
end RawLieIntegration
end

end OAI
