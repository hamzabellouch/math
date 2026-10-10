import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization

namespace OAI

/-! Conjugating the test homeomorphisms transports conformal removability
through a conformal Möbius homeomorphism. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem orientationPreserving_conjugate (e H : Sphere ≃ₜ Sphere)
    (hH : OrientationPreserving H) : OrientationPreserving ((e.trans H).trans e.symm) := by
  have hh := (ContinuousMap.Homotopic.refl (⟨e.symm,e.symm.continuous⟩ : C(Sphere,Sphere))).comp
    (hH.comp (ContinuousMap.Homotopic.refl (⟨e,e.continuous⟩ : C(Sphere,Sphere))))
  have hi : (⟨e.symm,e.symm.continuous⟩ : C(Sphere,Sphere)).comp
      ((ContinuousMap.id Sphere).comp (⟨e,e.continuous⟩ : C(Sphere,Sphere))) =
        ContinuousMap.id Sphere := by
    ext p
    exact e.symm_apply_apply p
  rw [hi] at hh
  exact hh

 theorem IsConformallyRemovable.image_mobius {E : Set Sphere}
    (hE : IsConformallyRemovable E) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (hM : ∀ p, e p = M • p)
    (he : ∀ p, IsConformalAt e p) (hi : ∀ p, IsConformalAt e.symm p) :
    IsConformallyRemovable (e '' E) := by
  refine ⟨hE.1.image e.continuous,?_⟩
  intro H hor hconf
  let K := (e.trans H).trans e.symm
  have hKconf : IsConformalOn K Eᶜ := by
    intro p hp
    have hpe : e p ∈ (e '' E)ᶜ := by
      rintro ⟨q,hq,heq⟩
      exact hp ((e.injective heq) ▸ hq)
    have hinner : IsConformalAt (H ∘ e) p := (hconf (e p) hpe).comp (he p)
    exact IsConformalAt.comp (f := H ∘ e) (g := e.symm) (hi (H (e p))) hinner
  obtain ⟨N,hN⟩ := hE.2 K (orientationPreserving_conjugate e H hor) hKconf
  refine ⟨M*N*M⁻¹,?_⟩
  intro q
  have h := congrArg e (hN (e.symm q))
  change e (e.symm (H (e (e.symm q)))) = e (N • e.symm q) at h
  simp only [e.apply_symm_apply] at h
  have hinv : e.symm q = M⁻¹ • q := by
    apply e.injective
    rw [e.apply_symm_apply,hM]
    simp
  rw [hM,hinv] at h
  simpa only [mul_smul] using h

 theorem IsConformallyRemovable.frontier_pointToInfinity {G : Set Sphere}
    (hG : IsConformallyRemovable (frontier G)) (p : Sphere) :
    IsConformallyRemovable (frontier (pointToInfinity p '' G)) := by
  rw [← (pointToInfinity p).image_frontier]
  exact hG.image_mobius (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p) (isConformalAt_pointToInfinity p)
    (isConformalAt_pointToInfinity_symm p)

end CircleDomainRigidity

end

end OAI
