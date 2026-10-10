import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! A quotient isomorphism obtained from a subgroup with prescribed image. -/
namespace FiniteLattice.CommonCore

variable {A H T : Type*} [Group A] [Group H] [Group T]

/-- Restrict `alpha` to `Q` and identify its image `J` with `T`. -/
def preimageMap (alpha : A →* H) (Q : Subgroup A) (J : Subgroup H)
    (himage : Q.map alpha = J) (e : T ≃* J) : Q →* T where
  toFun q := e.symm ⟨alpha q, by
    rw [← himage]
    exact ⟨q.val, q.property, rfl⟩⟩
  map_one' := by
    apply e.injective
    rw [e.apply_symm_apply, map_one]
    apply Subtype.ext
    exact alpha.map_one
  map_mul' q r := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, e.apply_symm_apply, e.apply_symm_apply]
    apply Subtype.ext
    exact alpha.map_mul q.val r.val

theorem preimageMap_surjective (alpha : A →* H) (Q : Subgroup A)
    (J : Subgroup H) (himage : Q.map alpha = J) (e : T ≃* J) :
    Function.Surjective (preimageMap alpha Q J himage e) := by
  intro t
  have ht : (e t).val ∈ Q.map alpha := by
    rw [himage]
    exact (e t).property
  obtain ⟨q, hq, hqt⟩ := ht
  refine ⟨⟨q, hq⟩, ?_⟩
  apply e.injective
  change e (e.symm _) = e t
  rw [e.apply_symm_apply]
  exact Subtype.ext hqt

/-- The kernel of the transported map consists of the elements killed by `alpha`. -/
theorem preimageMap_ker_iff (alpha : A →* H) (Q : Subgroup A)
    (J : Subgroup H) (himage : Q.map alpha = J) (e : T ≃* J) (q : Q) :
    q ∈ (preimageMap alpha Q J himage e).ker ↔ alpha q = 1 := by
  change preimageMap alpha Q J himage e q = 1 ↔ alpha q = 1
  constructor
  · intro h
    have he := congrArg e h
    change e (e.symm _) = e 1 at he
    rw [e.apply_symm_apply, map_one] at he
    exact congrArg Subtype.val he
  · intro h
    apply e.injective
    change e (e.symm _) = e 1
    rw [e.apply_symm_apply, map_one]
    exact Subtype.ext h

/-- The first isomorphism theorem identifies the quotient of `Q` by the kernel with `T`. -/
noncomputable def canonicalTheta (alpha : A →* H) (Q : Subgroup A)
    (J : Subgroup H) (himage : Q.map alpha = J) (e : T ≃* J) :
    (Q ⧸ (preimageMap alpha Q J himage e).ker) ≃* T :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (preimageMap_surjective alpha Q J himage e)

theorem canonicalTheta_mk (alpha : A →* H) (Q : Subgroup A)
    (J : Subgroup H) (himage : Q.map alpha = J) (e : T ≃* J) (q : Q) :
    canonicalTheta alpha Q J himage e (QuotientGroup.mk' _ q) =
      preimageMap alpha Q J himage e q := rfl

end FiniteLattice.CommonCore

end OAI
