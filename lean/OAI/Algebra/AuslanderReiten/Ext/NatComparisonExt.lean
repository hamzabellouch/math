import OAI.Algebra.AuslanderReiten.Resolutions.NatResolutionCochain
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (r+(n+1)) (r+n) ≫ f n)
include f in
def natComparisonAugmentation : P.complex.X r ⟶ X := by
  exact f 0 ≫ P.π.f 0

include hf

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem natComparison_augmented_cycle :
    P.complex.d (r+1) r ≫ natComparisonAugmentation P r f = 0 := by
  have h := congrArg (fun z => z ≫ P.π.f 0) (hf 0)
  change (f 1 ≫ P.complex.d 1 0) ≫ P.π.f 0 =
    (P.complex.d (r+1) r ≫ f 0) ≫ P.π.f 0 at h
  rw [Category.assoc, P.complex_d_comp_π_f_zero, CategoryTheory.Limits.comp_zero,
    Category.assoc] at h
  exact h.symm

include k in

theorem natComparison_endExt_eq :
    endExt P (natComparisonCocycle (k := k) P P r f hf) =
      P.extMk (natComparisonAugmentation P r f) (r+1) rfl (natComparison_augmented_cycle P r f hf) := by
  rw [endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show -(r : ℤ)+(r : ℤ)=0 by omega)).injective
  change (((natComparisonCocycle (k := k) P P r f hf).val.comp (Cochain.ofHom P.π')
    (add_zero (r : ℤ))).v (-(r : ℤ)) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom) =
    (Cochain.toSingleMk ((P.cochainComplexXIso (-(r : ℤ)) r rfl).hom ≫ natComparisonAugmentation P r f)
      (by omega : -(r : ℤ)+(r : ℤ)=0)).v (-(r : ℤ)) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.toSingleMk_v]
  rw [Cochain.comp_v _ _ _ (-(r : ℤ)) 0 0 (by omega) (by omega)]
  change ((natComparisonCochain P P r f).v (-(r : ℤ)) 0 (by omega) ≫ P.π'.f 0) ≫ _ = _
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let eᵣ := P.cochainComplexXIso (-(r : ℤ)) r (by omega)
  let e₀ := P.cochainComplexXIso 0 0 rfl
  change ((natComparisonCochain P P r f).v (-(r : ℤ)) 0 (by omega) ≫ P.π'.f 0) ≫ s.hom =
    (((P.cochainComplexXIso (-(r : ℤ)) r rfl).hom ≫ natComparisonAugmentation P r f) ≫ s.inv) ≫ s.hom
  refine (congrArg (fun v => (v ≫ P.π'.f 0) ≫ s.hom)
    (natComparisonCochain_v P P r f 0)).trans ?_
  refine (congrArg (fun v => ((eᵣ.hom ≫ f 0 ≫ e₀.inv) ≫ v) ≫ s.hom)
    P.π'_f_zero).trans ?_
  simp only [e₀, eᵣ, s, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
