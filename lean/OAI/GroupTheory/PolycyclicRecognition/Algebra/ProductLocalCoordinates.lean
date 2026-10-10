import OAI.GroupTheory.PolycyclicRecognition.Algebra.TranslationLocalHomeomorph
import Mathlib.Topology.Constructions.SumProd

namespace OAI

/-! # Extracting local coordinates from a product map

A local coordinate map of the form `(x,z) ↦ (f x,z)` supplies local
coordinates for `f`. This bridge works even when the target factor has no
manifold structure yet.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem local_coordinates_of_prodMap {f : X → Y} (x : X) (z : Z)
    (hinj : ∃ U ∈ 𝓝 (x, z), InjOn (fun p : X × Z => (f p.1, p.2)) U)
    (hmap : map (fun p : X × Z => (f p.1, p.2)) (𝓝 (x, z)) = 𝓝 (f x, z)) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ map f (𝓝 x) = 𝓝 (f x) := by
  constructor
  · obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨(fun y : X => (y, z)) ⁻¹' U, ?_, ?_⟩
    · exact (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU
    · intro a ha b hb hab
      exact congrArg Prod.fst (hi ha hb (Prod.ext hab rfl))
  · calc
      map f (𝓝 x) = map f (map Prod.fst (𝓝 (x, z))) := by rw [map_fst_nhds]
      _ = map (f ∘ Prod.fst) (𝓝 (x, z)) := map_map
      _ = map Prod.fst (map (fun p : X × Z => (f p.1, p.2)) (𝓝 (x, z))) :=
        map_map.symm
      _ = 𝓝 (f x) := by rw [hmap, map_fst_nhds]

theorem localHomeomorph_hom_of_prodMap
    {N K Q : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [TopologicalSpace Q]
    (f : N →* K) (q : Q)
    (hinj : ∃ U ∈ 𝓝 (1, q), InjOn (fun p : N × Q => (f p.1, p.2)) U)
    (hmap : map (fun p : N × Q => (f p.1, p.2)) (𝓝 (1, q)) = 𝓝 (1, q)) :
    IsLocalHomeomorph f := by
  let : Zero N := ⟨1⟩
  obtain ⟨hi, hm⟩ := local_coordinates_of_prodMap (f := f) 1 q hinj (by simpa using hmap)
  apply localHomeomorph_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) (by
      change map f (𝓝 (1 : N)) = 𝓝 (1 : K)
      simpa only [map_one] using hm) hi

end PolycyclicRecognition

end

end OAI
