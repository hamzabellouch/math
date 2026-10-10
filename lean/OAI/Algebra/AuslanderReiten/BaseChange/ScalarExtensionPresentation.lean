import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionHom

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {P Q M N : Type w}
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]
  [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower k R Q]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] scalarExtensionModule

omit [Module k P] [IsScalarTower k R P] [Module k Q] [IsScalarTower k R Q]
  [Module k M] [IsScalarTower k R M] in

theorem moduleHom_exact (d : Q →ₗ[R] P) (p : P →ₗ[R] M)
    (hex : Function.Exact d p) (hp : Function.Surjective p) :
    Function.Exact (LinearMap.lcomp k N p) (LinearMap.lcomp k N d) := by
  intro f
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  constructor
  · intro hf
    refine ⟨((LinearMap.range d).liftQ f (LinearMap.range_le_ker_iff.mpr hf)).comp
      (hex.linearEquivOfSurjective hp).symm.toLinearMap, ?_⟩
    ext x
    simp
  · rintro ⟨g, rfl⟩
    rw [LinearMap.comp_assoc, hex.linearMap_comp_eq_zero, LinearMap.comp_zero]

theorem scalarExtensionHom_bijective_of_presentation
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (d : Q →ₗ[R] P) (p : P →ₗ[R] M)
    (hex : Function.Exact d p) (hp : Function.Surjective p) :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  have hi : Function.Injective (LinearMap.lcomp k N p) :=
    LinearMap.lcomp_injective_of_surjective p hp
  have hbi := Module.Flat.lTensor_preserves_injective_linearMap (M := E) (LinearMap.lcomp k N p) hi
  have he := Module.Flat.lTensor_exact E (moduleHom_exact k R d p hex hp (N := N))
  have hpE := scalarExtensionMap_surjective k E R p hp
  have hiE : Function.Injective
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R p)) :=
    LinearMap.lcomp_injective_of_surjective _ hpE
  constructor
  · intro x y hxy
    apply hbi
    apply (scalarExtensionHom_bijective k E R (M := P) (N := N)).1
    change scalarExtensionHom k E R ((LinearMap.lcomp k N p).baseChange E x) =
      scalarExtensionHom k E R ((LinearMap.lcomp k N p).baseChange E y)
    simp only [scalarExtensionHom_precomp, hxy]
  · intro f
    obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective k E R (M := P) (N := N)).2
      (f.comp (scalarExtensionMap k E R p))
    have hz : (LinearMap.lcomp k N d).lTensor E x = 0 := by
      apply (scalarExtensionHom_bijective k E R (M := Q) (N := N)).1
      change scalarExtensionHom k E R ((LinearMap.lcomp k N d).baseChange E x) = _
      rw [scalarExtensionHom_precomp, hx, LinearMap.comp_assoc,
        ← scalarExtensionMap_comp, hex.linearMap_comp_eq_zero, map_zero]
      ext x
      simp [scalarExtensionMap]
    obtain ⟨y, hy⟩ := (he x).1 hz
    refine ⟨y, hiE ?_⟩
    change (scalarExtensionHom k E R y).comp (scalarExtensionMap k E R p) =
      f.comp (scalarExtensionMap k E R p)
    rw [← scalarExtensionHom_precomp]
    exact (congrArg (scalarExtensionHom k E R) hy).trans hx

theorem scalarExtensionHom_bijective_finite [Module.Finite k R] [Module.Finite R M] :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let : Module.Finite k (LinearMap.ker p) :=
    Module.Finite.of_injective ((LinearMap.ker p).subtype.restrictScalars k)
      (LinearMap.ker p).injective_subtype
  let : Module.Finite R (LinearMap.ker p) :=
    Module.Finite.of_restrictScalars_finite k R _
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R (LinearMap.ker p)
  let d := (LinearMap.ker p).subtype.comp q
  have hex : Function.Exact d p := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hq ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, rfl⟩
      exact (q y).property
  exact scalarExtensionHom_bijective_of_presentation k E R d p hex hp

end ArExplicit

end

end OAI
