import OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}

theorem closedModule_restrict_annihilated [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    RingHom.ker (J.subschemeι ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ((closedModule I).restrict U.1.ι,⊤) := by
  let : IsAffine U.1.toScheme := U.2
  have hcover : (I.comap U.1.ι).support ⊔ (J.comap U.1.ι).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    ext x
    change U.1.ι x ∈ (I.support : Set X) ∪ (J.support : Set X) ↔ True
    have hx : U.1.ι x ∈ (I.support ⊔ J.support : Closeds X) := by rw [h]; trivial
    exact iff_true_intro hx
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  let e := closedModuleRestrictIso I U.1.ι
  have hj : a ∈ (J.comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ := by
    erw [← (J.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩,
      ← ker_appTop_subscheme_morphismRestrict J U]
    exact ha
  have hz := Module.mem_annihilator.mp
    (ideal_le_annihilator_closedModule_of_reduced_cover hcover
      ⟨⊤,isAffineOpen_top _⟩ hj) (e.hom.app ⊤ m)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  exact (e.hom.app_smul a m).trans (hz.trans (map_zero _).symm)

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
