import OAI.RepresentationTheory.RestrictedTilting.LatticeNumerator

namespace OAI

namespace FiberFunctorProof
variable {R K ι : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [GCDMonoid R] [IsFractionRing R K] in
lemma lattice_swap_mem (x y : R) (P : (ι → K) ≃ₗ[K] (ι → K))
    {v : ι → K} (hv : v ∈ gluedLattice x y P) :
    P.symm v ∈ gluedLattice y x P.symm := by
  obtain ⟨h₁,w,h₂,hw⟩ := hv
  change P w = v at hw
  constructor
  · simpa only [← hw, LinearEquiv.symm_apply_apply] using h₂
  · exact ⟨v,h₁,rfl⟩

 

noncomputable def latticeSwap (x y : R) (P : (ι → K) ≃ₗ[K] (ι → K)) :
    gluedLattice x y P ≃ₗ[R] gluedLattice y x P.symm where
  toFun v := ⟨P.symm v.val, lattice_swap_mem x y P v.property⟩
  invFun v := ⟨P v.val, by
    simpa only [LinearEquiv.symm_symm] using lattice_swap_mem y x P.symm v.property⟩
  left_inv v := by apply Subtype.ext; exact P.apply_symm_apply v.val
  right_inv v := by apply Subtype.ext; exact P.symm_apply_apply v.val
  map_add' v w := by apply Subtype.ext; exact P.symm.map_add _ _
  map_smul' a v := by apply Subtype.ext; exact linearEquiv_map_base_smul P.symm a v.val

end FiberFunctorProof

end OAI
