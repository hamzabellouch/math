import OAI.Analysis.CircleDomains.Modulus.MobiusNormalization

namespace OAI

/-!
# Circle domains under the normalizing Möbius maps

Round complementary disks transform by multiplication of their defining
matrices. A homeomorphic Möbius map therefore preserves circle domains.
The explicit normalizer sends any prescribed sphere point to infinity.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem isCircleDomain_image_mobius
    {U : Set Sphere} (hU : IsCircleDomain U) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (he : ∀ p, e p = M • p) : IsCircleDomain (e '' U) := by
  refine ⟨e.isOpenMap _ hU.1, hU.2.1.image e e.continuous.continuousOn, ?_⟩
  intro p hp
  have hpre : e.symm p ∈ Uᶜ := by
    intro hx
    exact hp ⟨e.symm p, hx, e.apply_symm_apply p⟩
  have hcomponent : e '' connectedComponentIn Uᶜ (e.symm p) =
      connectedComponentIn (e '' U)ᶜ p := by
    rw [e.image_connectedComponentIn hpre, e.image_compl, e.apply_symm_apply]
  rcases hU.2.2 (e.symm p) hpre with ⟨q, hq⟩ | hround
  · left
    refine ⟨e q, ?_⟩
    rw [← hcomponent, hq, image_singleton]
  · right
    rw [← hcomponent]
    have hefun : (e : Sphere → Sphere) = fun x => M • x := funext he
    simpa only [hefun] using isRoundClosedDisk_image_mobius hround M

def pointToInfinity (p : Sphere) : Sphere ≃ₜ Sphere :=
  p.elim (Homeomorph.refl _) (fun z =>
    (affineSphere 1 (-z) one_ne_zero).trans CannonMobius.inversion)

def pointToInfinityMobius (p : Sphere) : Mobius :=
  p.elim 1 (fun z => inversionMobius * affineMobius 1 (-z) one_ne_zero)

theorem pointToInfinity_eq_smul (p q : Sphere) :
    pointToInfinity p q = pointToInfinityMobius p • q := by
  cases p using OnePoint.rec with
  | infty => simp [pointToInfinity, pointToInfinityMobius]
  | coe z =>
    change CannonMobius.inversion (affineSphere 1 (-z) one_ne_zero q) = _
    rw [inversion_eq_smul, affineSphere_eq_smul, ← mul_smul]
    rfl

theorem pointToInfinity_apply_self (p : Sphere) : pointToInfinity p p = OnePoint.infty := by
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change CannonMobius.inv (affineSphere 1 (-z) one_ne_zero (z : Sphere)) = OnePoint.infty
    have heq : affineSphere 1 (-z) one_ne_zero (z : Sphere) = ((0 : ℂ) : Sphere) := by
      simp [affineSphere, affineHomeomorph]
    rw [heq]
    exact CannonMobius.inv_zero

theorem pointToInfinity_preserves_circleDomain (p : Sphere)
    {U : Set Sphere} (hU : IsCircleDomain U) :
    IsCircleDomain (pointToInfinity p '' U) :=
  isCircleDomain_image_mobius hU (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p)

end CircleDomainRigidity

end

end OAI
