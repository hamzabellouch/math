import OAI.Algebra.AuslanderReiten.Coordinates.FiniteConnectingProducts
import OAI.Algebra.AuslanderReiten.HomComplex.FiniteFullHomExt
import OAI.Algebra.AuslanderReiten.Stable.StableExtNaturality

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def moduleExtSourceStableEquiv (N : ModuleCat.{u} R) (n : ℕ) :
    Ext M.carrier N (n+1) ≃+
      StableHom R (RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) N :=
  (extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm N (n+1)).toAddEquiv.trans
    ((positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain N n).toAddEquiv.trans
      (StableIsomorphism.ofLinearEquiv
        (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv)

private theorem source_selfExtIso (n : ℕ)
    (z : Ext (ModuleCat.of R (Cokernel (chainOfCochain (M.completeCochain τ)) 0))
      (ModuleCat.of R (Cokernel (chainOfCochain (M.completeCochain τ)) 0)) n) :
    extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm M.carrier n
      (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso n z) =
        z.comp (Ext.mk₀ (M.fullCokernelEquiv τ).toModuleIso.hom) (add_zero n) := by
  simp [extSourceIso, selfExtIso_apply]
  have hid : ModuleCat.ofHom (M.fullCokernelEquiv τ).toLinearMap ≫
      ModuleCat.ofHom (M.fullCokernelEquiv τ).symm.toLinearMap = 𝟙 _ :=
    (M.fullCokernelEquiv τ).toModuleIso.hom_inv_id
  rw [hid, Ext.mk₀_id_comp]

theorem moduleExtSourceStableEquiv_fullPositive (n : ℕ)
    (u : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) :
    moduleExtSourceStableEquiv τ M M.carrier n (fullPositiveModuleExtEquiv τ M n u) =
      resolutionSourceAtStableEquiv τ M M ((n+1 : ℕ) : ℤ) u := by
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain M.carrier n
      (extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm M.carrier (n+1)
        (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso (n+1)
          (fullPositiveExtEquiv (k := k) _ _ _ _ n u)))) = _
  rw [source_selfExtIso, positiveExtStableEquiv_postcomp, fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [fullHomSourceStableLinearEquiv_mk, resolutionSourceAtStableEquiv_mk,
    StableHom.postcomp_classOf]
  simp only [StableIsomorphism.sourceAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  rfl

theorem moduleExtSourceStableEquiv_extMk (N : ModuleCat.{u} R)
    (P : ProjectiveResolution M.carrier)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      (M.fullCokernelEquiv τ).toModuleIso.hom)
    (n : ℕ) (f : P.complex.X (n+1) ⟶ N)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] N)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    moduleExtSourceStableEquiv τ M N n (P.extMk f (n+2) rfl hf) =
      StableHom.classOf R _ _ t := by
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain N n
      ((Ext.mk₀ (M.fullCokernelEquiv τ).toModuleIso.hom).comp
        (P.extMk f (n+2) rfl hf) (zero_add _))) = _
  rw [ProjectiveResolution.mk₀_comp_extMk f (n+2) rfl hf φ,
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

theorem fullPositiveModuleExtEquiv_eq_extMk
    (P : ProjectiveResolution M.carrier)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      (M.fullCokernelEquiv τ).toModuleIso.hom)
    (n : ℕ) (f : P.complex.X (n+1) ⟶ M.carrier)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (u : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ))
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] M.carrier)
    (hu : resolutionSourceAtStableEquiv τ M M ((n+1 : ℕ) : ℤ) u = StableHom.classOf R _ _ t)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    fullPositiveModuleExtEquiv τ M n u = P.extMk f (n+2) rfl hf := by
  apply (moduleExtSourceStableEquiv τ M M.carrier n).injective
  rw [moduleExtSourceStableEquiv_fullPositive, hu,
    moduleExtSourceStableEquiv_extMk τ M M.carrier P φ n f hf t ht]

end ArExplicit.FiniteLeftModule

end

end OAI
