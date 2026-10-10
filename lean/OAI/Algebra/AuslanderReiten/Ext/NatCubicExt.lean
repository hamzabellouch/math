import OAI.Algebra.AuslanderReiten.Resolutions.NatResolutionCubic
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (n+4) (n+3) ≫ f n)
include hf

theorem natCubic_augmented_cycle : P.complex.d 4 3 ≫ (f 0 ≫ P.π.f 0) = 0 := by
  rw [← Category.assoc, ← hf 0, Category.assoc, P.complex_d_comp_π_f_zero,
    CategoryTheory.Limits.comp_zero]

variable [HasDerivedCategory (ModuleCat.{u} R)]

include k in

theorem natCubic_endExt_eq :
    endExt P (natCubicCocycle (k := k) P f hf) =
      P.extMk (f 0 ≫ P.π.f 0) 4 rfl (natCubic_augmented_cycle P f hf) := by
  rw [endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show (-3 : ℤ)+3=0 by omega)).injective
  change (((natCubicCocycle (k := k) P f hf).val.comp (Cochain.ofHom P.π')
    (add_zero 3)).v (-3) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom) =
    (Cochain.toSingleMk ((P.cochainComplexXIso (-3) 3 rfl).hom ≫ f 0 ≫ P.π.f 0)
      (by omega : (-3 : ℤ)+3=0)).v (-3) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.toSingleMk_v]
  rw [Cochain.comp_v _ _ _ (-3) 0 0 (by omega) (by omega)]
  change ((natCubicCochain P f).v (-3) 0 (by omega) ≫ P.π'.f 0) ≫ _ = _
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let e₃ := P.cochainComplexXIso (-3) 3 rfl
  let e₀ := P.cochainComplexXIso 0 0 rfl
  change ((natCubicCochain P f).v (-3) 0 (by omega) ≫ P.π'.f 0) ≫ s.hom =
    ((e₃.hom ≫ f 0 ≫ P.π.f 0) ≫ s.inv) ≫ s.hom
  refine (congrArg (fun v => (v ≫ P.π'.f 0) ≫ s.hom)
    (natCubicCochain_v P f 0)).trans ?_
  refine (congrArg (fun v => ((e₃.hom ≫ f 0 ≫ e₀.inv) ≫ v) ≫ s.hom)
    P.π'_f_zero).trans ?_
  simp only [e₀, e₃, s, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
