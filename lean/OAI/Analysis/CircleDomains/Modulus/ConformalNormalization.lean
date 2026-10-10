import OAI.Analysis.CircleDomains.Uniformization.MobiusConformal

namespace OAI

/-!
# Conformal point-to-infinity normalization

The explicit normalizer and its inverse are conformal in every sphere
chart. Postcomposition therefore preserves the conformal equivalence,
not just the topology and the round complementary components.
-/

open Set Function
open scoped OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem affineSphere_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    (affineSphere a b ha).symm = affineSphere a⁻¹ (-b / a) (inv_ne_zero ha) := by
  apply Homeomorph.ext
  intro p
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (((z - b) / a : ℂ) : Sphere) = ((a⁻¹ * z + -b / a : ℂ) : Sphere)
    congr 1
    ring

theorem isConformalAt_affineSphere_symm (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha).symm p := by
  rw [affineSphere_symm_eq]
  exact isConformalAt_affineSphere _ _ _ p

theorem isConformalAt_pointToInfinity (p q : Sphere) :
    IsConformalAt (pointToInfinity p) q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt (CannonMobius.inversion ∘ affineSphere 1 (-z) one_ne_zero) q
    exact (isConformalAt_inversion _).comp (isConformalAt_affineSphere _ _ _ q)

theorem isConformalAt_pointToInfinity_symm (p q : Sphere) :
    IsConformalAt (pointToInfinity p).symm q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt ((affineSphere 1 (-z) one_ne_zero).symm ∘ CannonMobius.inversion) q
    exact (isConformalAt_affineSphere_symm _ _ _ _).comp (isConformalAt_inversion q)

theorem isConformalEquivalence_of_homeomorph (e : Sphere ≃ₜ Sphere) (U : Set Sphere)
    (he : IsConformalOn e U) (hi : IsConformalOn e.symm (e '' U)) :
    IsConformalEquivalence e U (e '' U) := by
  refine ⟨he, mapsTo_image _ _, e.symm, hi, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply] using hp
  · intro p _
    exact e.symm_apply_apply p
  · intro p _
    exact e.apply_symm_apply p

theorem isConformalEquivalence_pointToInfinity (p : Sphere) (U : Set Sphere) :
    IsConformalEquivalence (pointToInfinity p) U (pointToInfinity p '' U) :=
  isConformalEquivalence_of_homeomorph _ U (fun q _ => isConformalAt_pointToInfinity p q)
    (fun q _ => isConformalAt_pointToInfinity_symm p q)

end CircleDomainRigidity

end

end OAI
