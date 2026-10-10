import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyExhaustionInjectivity
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Finite top homology forces an index-detecting exhaustion to stabilize -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule Rep.hV2 Rep.instLinear

theorem indexCoordinate_injective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (u : M ≃ₗ[ℤ] ℤ) (v : N ≃ₗ[ℤ] ℤ) (k : ℕ) (hk : k ≠ 0)
    (h : ∀ x, v (f x) = (k : ℤ) * u x) : Function.Injective f := by
  intro x y hxy
  apply u.injective
  apply mul_left_cancel₀ (show (k : ℤ) ≠ 0 by exact_mod_cast hk)
  rw [← h, ← h, hxy]

theorem indexCoordinate_surjective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (u : M ≃ₗ[ℤ] ℤ) (v : N ≃ₗ[ℤ] ℤ) (k : ℕ)
    (h : ∀ x, v (f x) = (k : ℤ) * u x) (hf : Function.Surjective f) : k = 1 := by
  obtain ⟨x, hx⟩ := hf (v.symm 1)
  have hd : (k : ℤ) ∣ 1 := ⟨u x, by rw [← h, hx, LinearEquiv.apply_symm_apply]⟩
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd)

theorem exhaustion_stabilizes_of_finite_homology
    {G : Type} [Group G] (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i : ℕ)
    [Module.Finite ℤ (groupHomology A i)]
    (hindex : ∀ n m, ((S n).subgroupOf (S m)).FiniteIndex)
    (hdegree : ∀ n m (hnm : n ≤ m),
      ∃ (u : groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ)
        (v : groupHomology (Rep.res (S m).subtype A) i ≃ₗ[ℤ] ℤ),
        ∀ x, v (groupHomology.map (Subgroup.inclusion (hS hnm))
          (subgroupRestrictionMap (hS hnm) A) i x) =
          (((S n).subgroupOf (S m)).index : ℤ) * u x) :
    ∃ n, S n = ⊤ := by
  have hinj n m (hnm : n ≤ m) : Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i) := by
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    let := hindex n m
    exact indexCoordinate_injective _ u v _ Subgroup.FiniteIndex.index_ne_zero h
  obtain ⟨n, hn⟩ := exists_surjective_homology_stage S hS hcover A i
  have hsurj := (ModuleCat.epi_iff_surjective (subgroupHomologyInclusion (S n) A i)).mp hn
  have heq m (hnm : n ≤ m) : S m = S n := by
    have hi := subgroupHomologyInclusion_injective_of_stages S hS hcover A i hinj m
    have ht : Function.Surjective (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj (subgroupHomologyInclusion (S m) A i y)
      refine ⟨x, hi ?_⟩
      exact (congrArg (fun f => f x) (subgroupHomologyInclusion_factor (hS hnm) A i)).trans hx
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    have hk := indexCoordinate_surjective _ u v _ h ht
    have hback : S m ≤ S n := (Subgroup.relIndex_eq_one).mp hk
    exact le_antisymm hback (hS hnm)
  refine ⟨n, top_unique ?_⟩
  intro g _
  obtain ⟨m, hm⟩ := hcover g
  have hgm := hS (le_max_right n m) hm
  rwa [heq (max n m) (le_max_left n m)] at hgm

end PolycyclicRecognition

end

end OAI
