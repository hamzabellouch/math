import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyExhaustionInjectivity

namespace OAI

/-! # Integral rank-one properties of the exhausted top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem exists_pair_in_homology_stage (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i : ℕ)
    (x y : groupHomology A i) :
    ∃ n, ∃ x' y' : groupHomology (Rep.res (S n).subtype A) i,
      subgroupHomologyInclusion (S n) A i x' = x ∧
        subgroupHomologyInclusion (S n) A i y' = y := by
  obtain ⟨n, x', hx⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
  obtain ⟨m, y', hy⟩ := exists_homologyClass_in_subgroup S hS hcover A i y
  refine ⟨max n m,
    groupHomology.map (Subgroup.inclusion (hS (le_max_left n m)))
      (subgroupRestrictionMap (hS (le_max_left n m)) A) i x',
    groupHomology.map (Subgroup.inclusion (hS (le_max_right n m)))
      (subgroupRestrictionMap (hS (le_max_right n m)) A) i y', ?_, ?_⟩
  · exact (congrArg (fun f => f x')
      (subgroupHomologyInclusion_factor (hS (le_max_left n m)) A i)).trans hx
  · exact (congrArg (fun f => f y')
      (subgroupHomologyInclusion_factor (hS (le_max_right n m)) A i)).trans hy

theorem homology_commensurable_of_rankOne_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hrank : ∀ n, Nonempty (groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ))
    (x y : groupHomology A i) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y := by
  obtain ⟨n, x', y', hx', hy'⟩ := exists_pair_in_homology_stage S hS hcover A i x y
  obtain ⟨e⟩ := hrank n
  have hxn : e x' ≠ 0 := by
    intro h
    have hz : x' = 0 := e.injective (h.trans (map_zero e).symm)
    exact hx (hx'.symm.trans (hz ▸ map_zero _))
  have hyn : e y' ≠ 0 := by
    intro h
    have hz : y' = 0 := e.injective (h.trans (map_zero e).symm)
    exact hy (hy'.symm.trans (hz ▸ map_zero _))
  have heq : (e y') • x' = (e x') • y' := by
    apply e.injective
    simp only [map_zsmul, zsmul_eq_mul]
    exact mul_comm _ _
  refine ⟨e y', e x', hyn, hxn, ?_⟩
  have he := congrArg (fun z => subgroupHomologyInclusion (S n) A i z) heq
  simpa only [map_zsmul, hx', hy'] using he

theorem homology_torsionFree_of_rankOne_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hrank : ∀ n, Nonempty (groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ))
    (hinj : ∀ n, Function.Injective (subgroupHomologyInclusion (S n) A i)) :
    ∀ (z : ℤ) (x : groupHomology A i), z • x = 0 → z = 0 ∨ x = 0 := by
  intro z x hzx
  obtain ⟨n, x', hx'⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
  obtain ⟨e⟩ := hrank n
  have hxz : z • x' = 0 := hinj n (by simpa only [map_zsmul, hx', map_zero] using hzx)
  have h := congrArg e hxz
  simp only [map_zsmul, map_zero, zsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with hz | hx
  · exact Or.inl hz
  · right
    have hx0 : x' = 0 := e.injective (hx.trans (map_zero e).symm)
    exact hx'.symm.trans (hx0 ▸ map_zero _)

theorem rankOne_homology_map_eq_zero_of_nonzero_kernel
    {M : ModuleCat ℤ}
    (htorsion : ∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (f : M ⟶ M) (x : M) (hx : x ≠ 0) (hfx : f x = 0) : f = 0 := by
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro y
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, b, _, hb, he⟩ := hcomm x y hx hy
  have hf := congrArg (fun z => f z) he
  simp only [map_zsmul, hfx, zsmul_zero] at hf
  exact (htorsion b (f y) hf.symm).resolve_left hb

end PolycyclicRecognition

end

end OAI
