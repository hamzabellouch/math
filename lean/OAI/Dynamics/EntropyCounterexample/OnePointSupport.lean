import Mathlib

namespace OAI

noncomputable section

open Set Filter Topology
open scoped OnePoint

namespace Problem340

def onePointZeroExtension {X Y E : Type*} [Zero E]
    (F : X → Y → E) (x : X) (z : OnePoint Y) : E :=
  z.elim 0 (F x)

@[simp] theorem onePointZeroExtension_infty {X Y E : Type*} [Zero E]
    (F : X → Y → E) (x : X) : onePointZeroExtension F x ∞ = 0 := rfl

@[simp] theorem onePointZeroExtension_coe {X Y E : Type*} [Zero E]
    (F : X → Y → E) (x : X) (z : Y) : onePointZeroExtension F x z = F x z := rfl

theorem onePointZeroExtension_zero_near_infty
    {X Y E : Type*} [TopologicalSpace Y] [T2Space Y] [Zero E]
    (F : X → Y → E) {K : Set Y} (hK : IsCompact K)
    (hzero : ∀ x y, y ∉ K → F x y = 0) :
    ∃ U : Set (OnePoint Y), IsOpen U ∧ (∞ : OnePoint Y) ∈ U ∧
      ∀ x z, z ∈ U → onePointZeroExtension F x z = 0 := by
  refine ⟨(OnePoint.some '' K)ᶜ,
    OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩,
    OnePoint.infty_notMem_image_coe, ?_⟩
  intro x z hz
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
      exact hzero x z (by simpa only [mem_compl_iff, OnePoint.coe_injective.mem_set_image]
        using hz)

theorem continuous_onePointZeroExtension
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace E] [Zero E]
    (F : X → Y → E) (hF : Continuous (Function.uncurry F))
    {K : Set Y} (hK : IsCompact K)
    (hzero : ∀ x y, y ∉ K → F x y = 0) :
    Continuous (fun p : X × OnePoint Y => onePointZeroExtension F p.1 p.2) := by
  obtain ⟨U, hU, hinfty, hUz⟩ := onePointZeroExtension_zero_near_infty F hK hzero
  rw [continuous_iff_continuousAt]
  rintro ⟨x, z⟩
  induction z using OnePoint.rec with
  | infty =>
      apply (continuousAt_const : ContinuousAt (fun _ : X × OnePoint Y => (0 : E))
        (x, ∞)).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hinfty)]
        with p hp
      exact hUz p.1 p.2 hp
  | coe z =>
      change Tendsto _ (𝓝 (x, (z : OnePoint Y))) (𝓝 (F x z))
      rw [nhds_prod_eq, OnePoint.nhds_coe_eq, prod_map_right, tendsto_map'_iff]
      change Tendsto (Function.uncurry F) (𝓝 x ×ˢ 𝓝 z) (𝓝 (F x z))
      rw [← nhds_prod_eq]
      exact hF.continuousAt

end Problem340

end

end OAI
