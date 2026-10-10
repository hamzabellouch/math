import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslationCovering
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # Inverting a local group isomorphism over a simply connected group

Local injectivity and the neighborhood-image identity at one suffice.
Translations propagate them, connectedness gives surjectivity, and the
proved covering-space argument gives the global inverse.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {N K : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

theorem surjective_of_hom_map_nhds_one [PreconnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1) : Function.Surjective f := by
  let : Zero N := ⟨1⟩
  have hm := map_nhds_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) hmap
  have hopen : IsOpenMap f := IsOpenMap.of_nhds_le fun n => (hm n).ge
  have hrange : IsOpen (f.range : Set K) := by
    simpa only [image_univ, MonoidHom.coe_range] using hopen univ isOpen_univ
  have hclosed := f.range.isClosed_of_isOpen hrange
  have hall : (f.range : Set K) = univ :=
    (show IsClopen (f.range : Set K) from ⟨hclosed, hrange⟩).eq_univ ⟨1, f.range.one_mem⟩
  intro k
  have hk : k ∈ f.range := by
    change k ∈ (f.range : Set K)
    rw [hall]
    trivial
  exact hk

theorem covering_of_hom_local_coordinates [PreconnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1)
    (hinj : ∃ U ∈ 𝓝 (1 : N), InjOn f U) : IsCoveringMap f := by
  let : Zero N := ⟨1⟩
  have hlocal := localHomeomorph_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) hmap hinj
  exact covering_of_translations (f := f) (R := fun n => Homeomorph.mulRight n)
    (hR := fun n m => f.map_mul m n) (hzero := f.map_one) (hf := hlocal)
    (hRinv := by
      change Continuous (fun p : N × N => p.2 * p.1⁻¹)
      exact continuous_snd.mul continuous_fst.inv)
    (hRcont := by
      change Continuous (fun p : N × N => p.2 * p.1)
      exact continuous_snd.mul continuous_fst)
    (L := fun n => Homeomorph.mulLeft n) (hL := fun n m => f.map_mul n m)
    (hsurj := surjective_of_hom_map_nhds_one f hmap)


theorem bijective_of_hom_local_coordinates [PreconnectedSpace N]
    [SimplyConnectedSpace K] [LocallyPathConnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1)
    (hinj : ∃ U ∈ 𝓝 (1 : N), InjOn f U) : Function.Bijective f := by
  let : Zero N := ⟨1⟩
  let cov := covering_of_hom_local_coordinates f hmap hinj
  exact (homeomorphOfSimplyConnectedCovering f cov).bijective

end PolycyclicRecognition

end

end OAI
