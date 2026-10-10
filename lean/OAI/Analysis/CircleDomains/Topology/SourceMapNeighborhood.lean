import OAI.Analysis.CircleDomains.Topology.JordanControlNeighborhood
import OAI.Analysis.CircleDomains.Topology.MapDiskExclusion
import OAI.Analysis.CircleDomains.Topology.JordanDiskImages

namespace OAI

/-! Open conditions on finitely many source traces retain compact target anchors,
Jordan sides, and separation from the compact set excluded from the energy integral. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_open_jordan_map_control
    {X : Type*} [TopologicalSpace X] (f₀ : C(X, ℂ))
    (γ : C(Circle, X)) (a : X) (H : ℂ ≃ₜ ℂ)
    (hfront : range (f₀.comp γ) = frontier (jordanInterior H))
    (ha : f₀ a ∈ jordanInterior H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∃ V : Set C(X, ℂ), IsOpen V ∧ f₀ ∈ V ∧
      ∀ f ∈ V, ∀ J : ℂ ≃ₜ ℂ,
        range (f.comp γ) = frontier (jordanInterior J) →
        f a ∈ jordanInterior J →
        K ⊆ jordanInterior J ∧ closure (jordanInterior J) ⊆ O := by
  obtain ⟨δ, hδ, hcontrol⟩ := exists_jordan_control_radius H (f₀.comp γ)
    (f₀.comp γ).continuous hfront ha hK hKH hO hHO
  let V : Set C(X, ℂ) :=
    {f | dist (f.comp γ) (f₀.comp γ) < δ} ∩ {f | dist (f a) (f₀ a) < δ}
  have hV : IsOpen V :=
    (isOpen_lt ((ContinuousMap.continuous_precomp γ).dist continuous_const)
      continuous_const).inter
      (isOpen_lt ((continuous_eval_const a).dist continuous_const)
        continuous_const)
  refine ⟨V, hV, ⟨by simpa using hδ, by simpa using hδ⟩, ?_⟩
  intro f hf J hJ haJ
  exact hcontrol (f.comp γ) (f a) J
    (fun t => (ContinuousMap.dist_apply_le_dist t).trans_lt hf.1) hf.2 hJ haJ

 theorem jordan_circle_range (H : ℂ ≃ₜ ℂ) :
    range (fun t : Circle => H (t : ℂ)) = frontier (jordanInterior H) := by
  rw [frontier_jordanInterior]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

 def sourceJordanCircle {G : Set Sphere} (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G) :
    C(Circle, FiniteSource G) :=
  ⟨fun t => ⟨H t, hH ((jordan_circle_range H).symm ▸ mem_range_self t)⟩,
    (H.continuous.comp continuous_subtype_val).subtype_mk _⟩

 theorem exists_open_source_anchor_control
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (ho₀ : ∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F₀ '' U))
    (hi₀ : InjOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    {K : Set ℂ} (hK : IsCompact K) (hKF : K ⊆ F₀ '' jordanInterior H) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧ finiteSourceMap F₀ hF₀ ∈ V ∧
      ∀ (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G)),
        finiteSourceMap F hF ∈ V →
        (∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F '' U)) →
        InjOn F (((↑) : ℂ → Sphere) ⁻¹' G) → K ⊆ F '' jordanInterior H := by
  obtain ⟨J₀, hJ₀, _, hJ₀front⟩ := exists_jordan_image_disk hsch
    (hG.preimage OnePoint.continuous_coe) hF₀ ho₀ hi₀ H hHG
  let γ := sourceJordanCircle H (frontier_subset_closure.trans hHG)
  have h0H : H 0 ∈ jordanInterior H := ⟨0, by simp, rfl⟩
  let a : FiniteSource G := ⟨H 0, hHG (subset_closure h0H)⟩
  have hfront : range ((finiteSourceMap F₀ hF₀).comp γ) =
      frontier (jordanInterior J₀) := by
    change range (F₀ ∘ (fun t : Circle => H (t : ℂ))) = _
    rw [range_comp, jordan_circle_range, hJ₀front]
  have ha : (finiteSourceMap F₀ hF₀) a ∈ jordanInterior J₀ :=
    hJ₀ ▸ mem_image_of_mem F₀ h0H
  obtain ⟨V, hV, hfV, hcontrol⟩ := exists_open_jordan_map_control
    (finiteSourceMap F₀ hF₀) γ a J₀ hfront ha hK (hJ₀ ▸ hKF)
    isOpen_univ (subset_univ _)
  refine ⟨V, hV, hfV, ?_⟩
  intro F hF hFV ho hi
  obtain ⟨J, hJ, _, hJfront⟩ := exists_jordan_image_disk hsch
    (hG.preimage OnePoint.continuous_coe) hF ho hi H hHG
  have hfront' : range ((finiteSourceMap F hF).comp γ) = frontier (jordanInterior J) := by
    change range (F ∘ (fun t : Circle => H (t : ℂ))) = _
    rw [range_comp, jordan_circle_range, hJfront]
  have ha' : (finiteSourceMap F hF) a ∈ jordanInterior J :=
    hJ ▸ mem_image_of_mem F h0H
  exact hJ.symm ▸ (hcontrol _ hFV J hfront' ha').1

 theorem isOpen_source_image_disjoint {G : Set Sphere}
    {P W : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) :
    IsOpen {f : C(FiniteSource G, ℂ) | Disjoint (f '' {x | x.val ∈ P}) W} := by
  have hPC : IsCompact {x : FiniteSource G | x.val ∈ P} := by
    apply Subtype.isCompact_iff.mpr
    have he : Subtype.val '' {x : FiniteSource G | x.val ∈ P} = P := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, hPG hz⟩, hz, rfl⟩
    rw [he]
    exact hP
  convert ContinuousMap.isOpen_setOfPred_mapsTo hPC hW.isOpen_compl using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.disjoint_left, Set.MapsTo, Set.mem_compl_iff,
    Set.forall_mem_image]

end CircleDomainRigidity

end

end OAI
