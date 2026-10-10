import Mathlib

namespace OAI

section
section
section
section
section
section
noncomputable section
namespace CannonRegularDisk
open Metric
open Set Metric Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev RoundSphere := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

section Topological
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def IsRegularDisk (U : Set X) : Prop :=
  ∃ (e : Plane → X), IsOpenEmbedding e ∧ ∃ (q : Plane) (r : ℝ),
    0<r ∧ U=e '' ball q r

lemma IsRegularDisk.isOpen {U : Set X} (hU : IsRegularDisk U) : IsOpen U := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  exact he.isOpenMap _ isOpen_ball

lemma IsRegularDisk.image {U : Set X} (hU : IsRegularDisk U) (f : X ≃ₜ Y) :
    IsRegularDisk (f '' U) := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  exact ⟨f ∘ e,f.isOpenEmbedding.comp he,q,r,hr,by rw [image_comp]⟩

lemma IsRegularDisk.preimage {U : Set Y} (hU : IsRegularDisk U) (f : X ≃ₜ Y) :
    IsRegularDisk (f ⁻¹' U) := by
  simpa only [Homeomorph.image_symm] using hU.image f.symm

end Topological

section Metric
variable {X : Type*} [MetricSpace X]

theorem IsRegularDisk.closed_certificate {U : Set X} (hU : IsRegularDisk U) :
    IsCompact (closure U) ∧ ∃ (e : Plane → X), IsOpenEmbedding e ∧
      ∃ (q : Plane) (r : ℝ), 0<r ∧ U=e '' ball q r ∧
        closure U=e '' closedBall q r ∧ frontier U=e '' sphere q r := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  have hc : closure (e '' ball q r)=e '' closedBall q r := by
    refine le_antisymm ?_ ?_
    · apply closure_minimal (image_mono ball_subset_closedBall)
      exact ((isCompact_closedBall q r).image he.continuous).isClosed
    · rw [←closure_ball q hr.ne']
      exact image_closure_subset_closure_image he.continuous
  have hf : frontier (e '' ball q r)=e '' sphere q r := by
    rw [frontier,interior_eq_iff_isOpen.mpr (he.isOpenMap _ isOpen_ball),hc,
      ←image_sdiff he.injective]
    congr 1
    ext z
    simp only [mem_sdiff,mem_closedBall,mem_ball,not_lt,mem_sphere]
    exact ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩
  exact ⟨hc ▸ (isCompact_closedBall q r).image he.continuous,e,he,q,r,hr,rfl,hc,hf⟩

lemma small_regular_disk (φ : X ≃ₜ RoundSphere) (x : X) {η : ℝ} (hη : 0<η) :
    ∃ U : Set X, IsRegularDisk U ∧ x ∈ U ∧ closure U ⊆ ball x η := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (-φ x)
  have ht : h.target=univ := stereographic'_target _
  have hx : φ x ∈ h.source := by
    rw [show h.source={-φ x}ᶜ from stereographic'_source _]
    exact ne_neg_of_mem_unit_sphere ℝ (φ x)
  let e : Plane → X := φ.symm ∘ h.symm
  have he : IsOpenEmbedding e := φ.symm.isOpenEmbedding.comp (h.symm.isOpenEmbedding ht)
  let q := h (φ x)
  have heq : e q=x := by
    dsimp [e,q]
    rw [h.left_inv hx,φ.symm_apply_apply]
  have hn : e ⁻¹' ball x η ∈ 𝓝 q := by
    apply he.continuous.continuousAt.preimage_mem_nhds
    rw [heq]
    exact ball_mem_nhds x hη
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let U := e '' ball q (r/2)
  have hU : IsRegularDisk U := ⟨e,he,q,r/2,half_pos hr,rfl⟩
  refine ⟨U,hU,⟨q,mem_ball_self (half_pos hr),heq⟩,?_⟩
  have hc : closure U ⊆ e '' closedBall q (r/2) := by
    apply closure_minimal (image_mono ball_subset_closedBall)
    exact ((isCompact_closedBall q (r/2)).image he.continuous).isClosed
  rintro y hy
  obtain ⟨z,hz,rfl⟩ := hc hy
  exact hsub (hz.trans_lt (half_lt_self hr))

theorem uniform_regular_disk_neighborhoods [CompactSpace X] (φ : X ≃ₜ RoundSphere)
    {η : ℝ} (hη : 0<η) :
    ∃ e : ℝ, 0<e ∧ ∀ x : X, ∃ U : Set X,
      IsRegularDisk U ∧ ball x e ⊆ U ∧ closure U ⊆ ball x η := by
  choose U hU hmem hsmall using fun x => small_regular_disk φ x (half_pos hη)
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,hmem x⟩
  obtain ⟨e,he,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x => (hU x).isOpen) hcover
  refine ⟨e,he,fun x => ?_⟩
  obtain ⟨p,hp⟩ := hLeb x (mem_univ x)
  have hxp : dist x p < η/2 := hsmall p (subset_closure (hp (mem_ball_self he)))
  refine ⟨U p,hU p,hp,?_⟩
  intro y hy
  have hyp := hsmall p hy
  have htri := dist_triangle y p x
  rw [dist_comm p x] at htri
  change dist y x<η
  change dist y p<η/2 at hyp
  linarith
end Metric
end CannonRegularDisk

end
end
end
end
end
end
end

end OAI
