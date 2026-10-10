import OAI.Algebra.AuslanderReiten.Coordinates.FiniteExtSourceCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

theorem moduleExtSourceStableEquiv_precomp_extMk (L N : ModuleCat.{u} R)
    (g : M.carrier ⟶ L) (P : ProjectiveResolution L)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      ((M.fullCokernelEquiv τ).toModuleIso.hom ≫ g))
    (n : ℕ) (f : P.complex.X (n+1) ⟶ N)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] N)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    moduleExtSourceStableEquiv τ M N n
      ((Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _)) =
      StableHom.classOf R _ _ t := by
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain N n
      ((Ext.mk₀ (M.fullCokernelEquiv τ).toModuleIso.hom).comp
        ((Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _)) (zero_add _))) = _
  rw [Ext.mk₀_comp_mk₀_assoc, ProjectiveResolution.mk₀_comp_extMk f (n+2) rfl hf φ,
    positiveExtStableEquiv_extMk]
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (StableHom.classOf R _ _ _) = _
  simp only [StableIsomorphism.sourceAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((M.completeCochain τ).d (-(((n+1 : ℕ) : ℤ)+1))
      (-((n+1 : ℕ) : ℤ))).hom) z
  exact (ht z).symm

theorem fullPositiveModuleExtEquiv_eq_precomp_extMk
    (L : ModuleCat.{u} R) (g : M.carrier ⟶ L) (P : ProjectiveResolution L)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      ((M.fullCokernelEquiv τ).toModuleIso.hom ≫ g))
    (n : ℕ) (f : P.complex.X (n+1) ⟶ M.carrier)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (u : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ))
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] M.carrier)
    (hu : resolutionSourceAtStableEquiv τ M M ((n+1 : ℕ) : ℤ) u = StableHom.classOf R _ _ t)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    fullPositiveModuleExtEquiv τ M n u =
      (Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _) := by
  apply (moduleExtSourceStableEquiv τ M M.carrier n).injective
  rw [moduleExtSourceStableEquiv_fullPositive, hu,
    moduleExtSourceStableEquiv_precomp_extMk τ M L M.carrier g P φ n f hf t ht]

end ArExplicit.FiniteLeftModule

end

end OAI
