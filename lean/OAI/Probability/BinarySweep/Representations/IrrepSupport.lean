import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps
namespace Irrep

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) [ρ.IsIrreducible]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma invariant_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V)
    (v : V) (hv : ∀ g, ρ g v = v) : v = 0 := by
  let f : Representation.IntertwiningMap (1 : Representation ℂ G ℂ) ρ :=
    (LinearMap.toSpanSingleton ℂ V v).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g c
      simp only [MonoidHom.one_apply, Module.End.one_apply, LinearMap.toSpanSingleton_apply,
        map_smul, hv])
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hf | hf
  · have hd := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf
    simp only [Module.finrank_self] at hd
    omega
  · have hh := congrArg (fun a : Representation.IntertwiningMap
        (1 : Representation ℂ G ℂ) ρ => a (1 : ℂ)) hf
    simpa [f] using hh

omit [FiniteDimensional ℂ V] in
lemma sum_apply_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) (x : V) :
    ∑ g : G, ρ g x = 0 := by
  apply invariant_eq_zero_of_finrank_gt_one ρ hD
  intro g
  simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h : G => ρ h x)

omit [FiniteDimensional ℂ V] in
lemma sum_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) :
    ∑ g : G, ρ g = 0 := by
  ext x
  simpa using sum_apply_eq_zero_of_finrank_gt_one ρ hD x

include ρ in
omit [FiniteDimensional ℂ V] in
lemma finrank_le_card : Module.finrank ℂ V ≤ Fintype.card G := by
  let : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  let f : ℂ[G] →ₗ[ℂ] ρ.asModule :=
    (LinearMap.toSpanSingleton ℂ[G] ρ.asModule v).restrictScalars ℂ
  have hf : Function.Surjective f := IsSimpleModule.toSpanSingleton_surjective ℂ[G] hv
  have hd := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  have he : Module.finrank ℂ ρ.asModule = Module.finrank ℂ V :=
    ρ.asModuleEquiv.finrank_eq
  rw [he] at hd
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)] at hd
  exact hd

end Irrep
end BinaryCoordinateSweeps

end

end OAI
