import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ProductChains

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialH0
open FreeChains

variable {X Y : SSet}
@[reassoc] lemma natural (f : X ⟶ Y) : SSet.homologyMap f Z 0 ≫ Y.homology₀ε Z=X.homology₀ε Z := by
  apply (cancel_epi ((X.chainComplex Z).homologyπ 0)).mp
  apply (cancel_epi (X.chainComplex Z).cycles₀Iso.inv).mp
  apply Sigma.hom_ext
  intro x
  have he : X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv =
      (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex Z).iCycles 0)).mp
    simp
  change X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv ≫ _ =
    X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv ≫ _
  simp only [←Category.assoc]
  rw [he]
  simp only [Category.assoc]
  change _ ≫ _ ≫ homologyMap (SSet.chainComplexMap f Z) 0 ≫ _ = _
  rw [homologyπ_naturality_assoc,liftCycles_comp_cyclesMap_assoc,SSet.ι_chainComplexMap_f]
  simp
noncomputable def augmentation : SSet.homologyFunctor Z 0 ⟶ (Functor.const SSet).obj Z where
  app X := X.homology₀ε Z
  naturality source target morphism := by
    change SSet.homologyMap morphism Z 0 ≫ target.homology₀ε Z =
      source.homology₀ε Z ≫ 𝟙 Z
    simpa only [Category.comp_id] using natural morphism
noncomputable def connectedIso (T : SimplicialObject SSet.{0}) (hT : ∀ n,(T.obj n).IsConnected) :
    T ⋙ SSet.homologyFunctor Z 0 ≅ (Functor.const SimplexCategoryᵒᵖ).obj Z :=
  by
    let f : T ⋙ SSet.homologyFunctor Z 0 ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Z :=
      { app n := (T.obj n).homology₀ε Z
        naturality n m g := by
          change SSet.homologyMap (T.map g) Z 0 ≫ (T.obj m).homology₀ε Z =
            (T.obj n).homology₀ε Z ≫ 𝟙 Z
          simpa only [Category.comp_id] using natural (T.map g) }
    have : ∀ n, IsIso (f.app n) := fun n => by
      have : (T.obj n).IsConnected := hT n
      change IsIso ((T.obj n).homology₀ε Z)
      infer_instance
    have : IsIso f := NatIso.isIso_of_isIso_app f
    exact asIso f
end SimplicialH0
example (X : SSet) [X.IsConnected] : IsIso (X.homology₀ε FreeChains.Z) := by infer_instance

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

abbrev D := SimplexCategory × SimplexCategory
variable (X : Dᵒᵖ ⥤ Type)
noncomputable def rowIso (q : ℕ) : TotalFiniteness.row (EilenbergZilber.twoComplex X) q ≅
    AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial X ⋙ SSet.homologyFunctor Z q) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_
  intro n m hnm
  obtain rfl : n=m+1 := hnm.symm
  simp only [Iso.refl_hom]
  change _ = (homologyFunctor A c q).map
    ((AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial (X ⋙ sigmaConst.obj Z) ⋙ alternatingFaceMapComplex A)).d (m+1) m)
  simp only [AlternatingFaceMapComplex.obj_d_eq,Functor.map_sum,Functor.map_zsmul]
  rfl
noncomputable def zeroRowIso (hX : ∀ n, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n)) :
    TotalFiniteness.row (EilenbergZilber.twoComplex X) 0 ≅
      AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj Z) :=
  rowIso X 0 ≪≫ (alternatingFaceMapComplex A).mapIso
    (SimplicialH0.connectedIso (EilenbergZilber.bisimplicial X) hX)
lemma zeroRow_vanish (hX : ∀ n, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n))
    (p : ℕ) (hp : p≠0) : IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const Z).homotopyEquiv
  exact IsZero.of_iso (AugmentedSplit.uni_isZero p hp)
    (((homologyFunctor A c p).mapIso (zeroRowIso X hX)) ≪≫ e.toHomologyIso p)
end BarHomology

end

section
open CategoryTheory Limits HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

lemma finite_homology (K : ChainComplex A ℕ) (n : ℕ) [Module.Finite ℤ (K.X n)] :
    Module.Finite ℤ (K.homology n) := by
  have : Module.Finite ℤ (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
lemma zero_homology (K : ChainComplex A ℕ) (n : ℕ) (hz : IsZero (K.X n)) :
    IsZero (K.homology n) := ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) hz
variable (X : Dᵒᵖ ⥤ Type)
lemma E2_finite (p q : ℕ) [Module.Finite ℤ
    (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)] :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) := by
  have : Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).X p) := by
    change Module.Finite ℤ (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)
    infer_instance
  exact finite_homology _ p
lemma E2_zero (p q : ℕ) (hz : IsZero
    (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)) :
    IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) :=
  zero_homology _ p hz

lemma connectivity (d : ℕ)
    (hc : ∀ n,SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n))
    (hz : ∀ q, 0 < q → IsZero (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋0⦌)) Z q))
    (hr : ∀ p q, 0 < q → q < d → IsZero (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q))
    (n : ℕ) (hn : 0 < n) (hd : n < d+1) :
    Subsingleton (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n) := by
  apply EilenbergZilber.subsingleton_diagonal X n
  intro p q hpq
  by_cases hq : q=0
  · subst q
    exact (ModuleCat.isZero_iff_subsingleton).mp (zeroRow_vanish X hc p (by omega))
  · have h : IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) := by
      by_cases hp : p=0
      · subst p; exact E2_zero X 0 q (hz q (by omega))
      · exact E2_zero X p q (hr p q (by omega) (by omega))
    exact (ModuleCat.isZero_iff_subsingleton).mp h

lemma finite (r : ℕ)
    (hc : ∀ n,SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n))
    (hz : ∀ q, 0 < q → IsZero (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋0⦌)) Z q))
    (hr : ∀ p q, 0 < q → q ≤ r → Module.Finite ℤ (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q))
    (n : ℕ) (hn : 0 < n) (hd : n ≤ r+1) :
    Module.Finite ℤ (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n) := by
  apply EilenbergZilber.finite_diagonal X n
  intro p q hpq
  by_cases hq : q=0
  · subst q
    have := (ModuleCat.isZero_iff_subsingleton).mp (zeroRow_vanish X hc p (by omega))
    infer_instance
  · by_cases hp : p=0
    · subst p
      have := (ModuleCat.isZero_iff_subsingleton).mp (E2_zero X 0 q (hz q (by omega)))
      infer_instance
    · have := hr p q (by omega) (by omega)
      exact E2_finite X p q
end BarHomology

end

end

end OAI
