import OAI.NumberTheory.PiExponent.Cohomology.GradedCech
import OAI.NumberTheory.PiExponent.Cohomology.GradedCechRecovery
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading

namespace OAI

namespace PiExponent.GradedCechExactness
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationExact
variable {R K F M σR σK σF σM J : Type*} [CommRing R]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
  [AddCommGroup M] [Module R M]
  [SetLike σR R]
  [SetLike σK K] [AddSubgroupClass σK K]
  [SetLike σF F] [AddSubgroupClass σF F]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓚 : ℤ → σK) (𝓕 : ℤ → σF) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓚]
  [SetLike.GradedSMul 𝒜 𝓕] [SetLike.GradedSMul 𝒜 𝓜]
  [DirectSum.Decomposition 𝓚] [DirectSum.Decomposition 𝓕] [DirectSum.Decomposition 𝓜]
  [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)
  (f : K →ₗ[R] F) (g : F →ₗ[R] M)
  (hf : ∀ i z, f (DirectSum.decompose 𝓚 z i : K) =
    (DirectSum.decompose 𝓕 (f z) i : F))
  (hg : ∀ i z, g (DirectSum.decompose 𝓕 z i : F) =
    (DirectSum.decompose 𝓜 (g z) i : M))
  (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g)

include hf hg hinj hex hsurj in

theorem augmentation_recovery_of_shortExact (d : ℤ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d 0,
      differential 𝒜 𝓕 x hx d c = 0 → ∃ p : 𝓕 d, augmentation 𝒜 𝓕 x hx d p = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d 1,
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d 0,
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d 0,
      differential 𝒜 𝓜 x hx d c = 0 → ∃ m : 𝓜 d, augmentation 𝒜 𝓜 x hx d m = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  apply GradedCechRecovery.augmentation_surjective_on_closed
    (differentialHom 𝒜 𝓚 x hx d 0) (differentialHom 𝒜 𝓚 x hx d 1)
    (differentialHom 𝒜 𝓕 x hx d 0) (differentialHom 𝒜 𝓕 x hx d 1)
    (differentialHom 𝒜 𝓜 x hx d 0)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 0) (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 1)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 2)
    (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 0) (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 1)
    (augmentation 𝒜 𝓕 x hx d) (augmentation 𝒜 𝓜 x hx d)
    (globalPieceMap 𝓕 𝓜 g pg d)
  · exact cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d 0 g hg hsurj
  · intro c hc
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 1 f g hf hg hex c).mp hc
  · exact cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d 2 hinj
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact cochainMap_differential 𝒜 𝓕 x hx 𝓜 g pg d c
  · intro c
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 0 f g hf hg hex).apply_apply_eq_zero c
  · exact differential_squared 𝒜 𝓕 x hx d
  · intro p
    exact (augmentation_natural 𝒜 𝓕 x hx 𝓜 g pg d p).symm
  · exact hfree
  · exact hkernel

include hf hg hinj hex hsurj in

theorem primitives_of_shortExact (d : ℤ) (q : ℕ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d (q + 1),
      differential 𝒜 𝓕 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓕 x hx d q,
        differential 𝒜 𝓕 x hx d b = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d (q + 1 + 1),
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d (q + 1),
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d (q + 1),
      differential 𝒜 𝓜 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓜 x hx d q,
        differential 𝒜 𝓜 x hx d b = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  intro c hc
  obtain ⟨b, hb⟩ := cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d (q + 1) g hg hsurj c
  have hdb : cochainMap 𝒜 𝓕 x hx 𝓜 g pg d (q + 1 + 1)
      (differential 𝒜 𝓕 x hx d b) = 0 := by
    rw [cochainMap_differential, hb, hc]
  obtain ⟨a, ha⟩ := (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1 + 1)
    f g hf hg hex (differential 𝒜 𝓕 x hx d b)).mp hdb
  have hclosed : differential 𝒜 𝓚 x hx d a = 0 := by
    apply cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d (q + 1 + 1 + 1) hinj
    rw [map_zero, cochainMap_differential, ha, differential_squared]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : differential 𝒜 𝓕 x hx d
      (b - cochainMap 𝒜 𝓚 x hx 𝓕 f pf d (q + 1) v) = 0 := by
    rw [differential_sub, ← cochainMap_differential, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree _ hcorrected
  refine ⟨cochainMap 𝒜 𝓕 x hx 𝓜 g pg d q p, ?_⟩
  rw [← cochainMap_differential, hp, map_sub,
    (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1) f g hf hg hex).apply_apply_eq_zero,
    sub_zero, hb]

end
end PiExponent.GradedCechExactness

end OAI
