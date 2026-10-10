import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Basic

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} k)]
variable [∀ i, Module.Projective Aᵐᵒᵖ (rightTerm k A Q (p i))]

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} A)] in
/-- The proved actual total functor sends every quasi-isomorphism to an isomorphism after localization. -/
theorem finiteTotal_inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).IsInvertedBy
    (finiteTotalFunctor k A Q p hp ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  let := finiteTotalMap_quasiIso k A Q f p hp
  exact (inferInstance : IsIso (DerivedCategory.Q.map (finiteTotalMap k A Q p hp f)))

/-- Localization of the actual signed total tensor functor, justified by the proved preservation theorem. -/
def derivedFiniteTotal : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} k) :=
  Localization.lift (finiteTotalFunctor k A Q p hp ⋙ DerivedCategory.Q)
    (finiteTotal_inverts k A Q p hp) DerivedCategory.Q

/-- The explicit natural comparison with the actual chain-level total on every input complex. -/
def derivedFiniteTotalComparison :
    DerivedCategory.Q ⋙ derivedFiniteTotal k A Q p hp ≅ finiteTotalFunctor k A Q p hp ⋙ DerivedCategory.Q :=
  Localization.fac (finiteTotalFunctor k A Q p hp ⋙ DerivedCategory.Q)
    (finiteTotal_inverts k A Q p hp) DerivedCategory.Q
end LittleFinitistic.ComplexTensor

end

end OAI
