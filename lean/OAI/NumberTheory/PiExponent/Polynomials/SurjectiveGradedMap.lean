import Mathlib

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum HomogeneousLocalization
open scoped HomogeneousIdeal

variable {A B S T : Type*} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

theorem gradedMap_homogeneous_lift (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {n : ℕ} {y : B} (hy : y ∈ ℬ n) : ∃ x, x ∈ 𝒜 n ∧ f x = y := by
  obtain ⟨x, hx⟩ := hf y
  refine ⟨decompose 𝒜 x n, (decompose 𝒜 x n).2, ?_⟩
  rw [f.map_directSumDecompose, hx]
  exact decompose_of_mem_same ℬ hy

theorem gradedMap_irrelevant_le_map (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn y hy
  obtain ⟨x, hx, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hx)

theorem homogeneousAway_map_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map f s) := by
  intro x
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective _ (f.map_mem hs) x
  obtain ⟨p, hp, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact ⟨Away.mk _ hs n p hp, Away.map_mk f s hs n p hp⟩

end PiExponent

end

end OAI
