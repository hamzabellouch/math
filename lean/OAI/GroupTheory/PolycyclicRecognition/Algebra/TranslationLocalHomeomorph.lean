import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Algebra.Group.Basic

namespace OAI

/-! # Propagating local coordinates by translations -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {V G : Type*} [TopologicalSpace V] [Zero V]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (f : V → G) (L : V → V ≃ₜ V)
  (hL0 : ∀ a, L a 0 = a)
  (hprod : ∀ a x, f (L a x) = f a * f x)
  (hmap : Filter.map f (𝓝 0) = 𝓝 (1 : G))

include L hL0 hprod hmap

theorem map_nhds_of_translations (a : V) : Filter.map f (𝓝 a) = 𝓝 (f a) := by
  have heq : f ∘ L a = (Homeomorph.mulLeft (f a)) ∘ f := funext (hprod a)
  calc
    Filter.map f (𝓝 a) = Filter.map f (Filter.map (L a) (𝓝 0)) := by
      rw [(L a).map_nhds_eq, hL0]
    _ = Filter.map (f ∘ L a) (𝓝 0) := Filter.map_map
    _ = Filter.map (Homeomorph.mulLeft (f a) ∘ f) (𝓝 0) := by rw [heq]
    _ = Filter.map (Homeomorph.mulLeft (f a)) (Filter.map f (𝓝 0)) := Filter.map_map.symm
    _ = 𝓝 (f a) := by rw [hmap, (Homeomorph.mulLeft (f a)).map_nhds_eq]; simp

theorem localHomeomorph_of_translations
    (hinj : ∃ U ∈ 𝓝 (0 : V), InjOn f U) : IsLocalHomeomorph f := by
  have hm := map_nhds_of_translations f L hL0 hprod hmap
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun a => (hm a).le
  have ho : IsOpenMap f := IsOpenMap.of_nhds_le fun a => (hm a).ge
  obtain ⟨U, hU, hi⟩ := hinj
  obtain ⟨W, hWU, hW, h0W⟩ := mem_nhds_iff.mp hU
  apply IsLocalHomeomorph.mk
  intro a
  let S : Set V := L a '' W
  have hS : IsOpen S := (L a).isOpenMap W hW
  have haS : a ∈ S := ⟨0, h0W, hL0 a⟩
  have hiS : InjOn f S := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    apply congrArg (L a)
    apply hi (hWU hx) (hWU hy)
    rw [hprod, hprod] at he
    exact mul_left_cancel he
  let e := OpenPartialHomeomorph.ofContinuousOpen hiS.toPartialEquiv hc.continuousOn ho hS
  exact ⟨e, haS, fun _ _ => rfl⟩

end PolycyclicRecognition

end

end OAI
