import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.MaximalCartier

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem maximal_cartier_extraction_of_iso (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L M : LineBundle X) (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U eM (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U eM (sectionCombination k s v))^j *
        affineCoefficient U (localPowerFrame U.1 e n) q) (affineCoefficient U eA t) := by
  let s' := fun i => (Iso.refl (O X)).hom ≫ s i ≫ E.hom
  have hs' := twistedSections_cover (Iso.refl (O X)) E s hs
  have hI := sectionIdeal_twist k (Iso.refl (O X)) E s hs v
  have hc : sectionCombination k s' v = sectionCombination k s v ≫ E.hom := by
    simp only [sectionCombination,s',Iso.refl_hom,Category.id_comp,
      Preadditive.sum_comp,Category.assoc]
  have hn : sectionCombination k s' v ≠ 0 := by
    rw [hc]
    exact fun h => hne ((cancel_mono E.hom).mp (by simpa using h))
  let : IsIntegral (sectionIdeal k s' hs' v).subscheme := by rw [hI]; infer_instance
  let : Nonempty ((sectionIdeal k s' hs' v).subschemeι ⁻¹ᵁ U.1).toScheme := by
    rw [hI]; infer_instance
  have hass : Associated (affineCoefficient U eM (sectionCombination k s v))
      (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s' v)) := by
    have coefficient_eq := congrArg
      (fun globalSection : O X ⟶ (L.pow d).sheaf =>
        affineCoefficient U (localPowerFrame U.1 e d) globalSection) hc
    exact coefficient_eq.symm ▸ affineCoefficient_iso U eM _ E _
  have hnu' : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s' v)) :=
    fun h => hnu (hass.isUnit_iff.mpr h)
  obtain ⟨j,n,ha,q,hq,hqv,hqass⟩ :=
    maximal_cartier_extraction p L d hd k s' hs' v hn U e hnu' a t ht
  rw [hI] at hqv
  refine ⟨j,n,ha,q,hq,hqv,?_⟩
  exact (((hass.pow_pow (n := j)).mul_right _).trans hqass).trans
    (affineCoefficient_change U _ eA t)
end
end MaximalSeshadri.Geometry

end

end OAI
