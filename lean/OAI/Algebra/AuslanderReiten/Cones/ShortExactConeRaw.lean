import OAI.Algebra.AuslanderReiten.Homology.ShortExactNaturality

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex CochainComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]

namespace CompleteComparison
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyRawEquiv_id (hK : TotallyAcyclicComplex (chainOfCochain K)) :
    cochainHomotopyRawEquiv hK hK.toExactProjectiveComplex (𝟙 _) =
      StableHom.classOf R _ _ LinearMap.id := by
  rw [← (HomotopyCategory.quotient _ _).map_id, cochainHomotopyRawEquiv_map]
  congr 1
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (K.d (-1) 0).hom) z
  rfl
end CompleteComparison

variable [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConeInverse_stable_identity (κ : H ⟶ mappingCone φ)
    (hκ : (HomotopyCategory.quotient _ _).map κ =
      (shortExactConeIso φ p he hF hG hH hi hp).inv) :
    StableHom.classOf R _ _ ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)) =
      StableHom.classOf R _ _ LinearMap.id := by
  have h : (HomotopyCategory.quotient _ _).map κ ≫
      (shortExactConeIso φ p he hF hG hH hi hp).hom = 𝟙 _ := by
    rw [hκ, Iso.inv_hom_id]
  have h' := congrArg (cochainHomotopyRawEquiv hH.to_chain hH.to_chain.toExactProjectiveComplex) h
  rw [cochainHomotopyRawEquiv_comp hH
    (mappingCone_totallyAcyclic φ hF hG) hH.toExactProjectiveCochain,
    shortExactConeIso_raw_hom, cochainHomotopyRawEquiv_map,
    StableHom.comp_classOf, cochainHomotopyRawEquiv_id] at h'
  exact h'

end ArExplicit

end

end OAI
