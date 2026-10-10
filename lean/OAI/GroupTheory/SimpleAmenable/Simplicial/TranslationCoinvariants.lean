import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TranslationNerve

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains Representation

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def orbitRaw (n:ℕ) : ((complex P).X n).V →ₗ[ℤ] (B P n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun s:ComposableArrows (C P) n=>s ⋙ ActionCategory.π P (Q P)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap
lemma orbitRaw_single (n:ℕ) (s:ComposableArrows (C P) n) (z:ℤ) :
    orbitRaw P n (MonoidAlgebra.single s z)=Finsupp.single (s ⋙ ActionCategory.π P (Q P)) z := by
  change Finsupp.lmapDomain ℤ ℤ _ (Finsupp.single s z)=_
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
lemma orbitRaw_invariant (n:ℕ) (q:Q P) : orbitRaw P n ∘ₗ ((complex P).X n).ρ q=orbitRaw P n := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change orbitRaw P n (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋n⦌)) q
    (MonoidAlgebra.single s 1)) = orbitRaw P n (MonoidAlgebra.single s 1)
  erw [Representation.linearize_single,orbitRaw_single,orbitRaw_single]
  exact congrArg (fun t => Finsupp.single t (1:ℤ)) (smul_project P n q s)
noncomputable def orbitForward (n:ℕ) : (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) ⟶
    (ModuleCat.free ℤ).obj (B P n) :=
  ModuleCat.ofHom (Coinvariants.lift _ (orbitRaw P n) (orbitRaw_invariant P n))
noncomputable def orbitBackward (n:ℕ) : (ModuleCat.free ℤ).obj (B P n) ⟶
    (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) :=
  ModuleCat.freeDesc (↾fun s=>Coinvariants.mk _ (MonoidAlgebra.single (lift P n 1 s) 1))
lemma orbitForward_mk (n:ℕ) (s:ComposableArrows (C P) n) (z:ℤ) :
    orbitForward P n (Coinvariants.mk _ (MonoidAlgebra.single s z)) =
      Finsupp.single (s ⋙ ActionCategory.π P (Q P)) z := orbitRaw_single P n s z
lemma orbitBackward_mk (n:ℕ) (s:B P n) : orbitBackward P n (ModuleCat.freeMk s)=
    Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single (lift P n 1 s) 1) :=
  ModuleCat.freeDesc_apply _ s
lemma mk_lift_one (n:ℕ) (s:ComposableArrows (C P) n) :
    Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single (lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1) =
      Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single s 1) := by
  have h := Coinvariants.mk_self_apply ((complex P).X n).ρ s.left.back
    (MonoidAlgebra.single (lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1)
  change Coinvariants.mk _ (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋n⦌)) s.left.back _)=_ at h
  erw [Representation.linearize_single] at h
  change Coinvariants.mk ((complex P).X n).ρ
    (MonoidAlgebra.single (s.left.back • lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1)=_ at h
  erw [smul_lift,mul_one,lift_recover] at h
  exact h.symm
noncomputable def orbitIso (n:ℕ) : (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) ≅
    (ModuleCat.free ℤ).obj (B P n) where
  hom := orbitForward P n
  inv := orbitBackward P n
  hom_inv_id := by
    apply Rep.coinvariantsFunctor_hom_ext
    apply ModuleCat.hom_ext
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change orbitBackward P n (orbitForward P n (Coinvariants.mk _ (MonoidAlgebra.single s 1))) =
      Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single s 1)
    erw [orbitForward_mk]
    change orbitBackward P n (ModuleCat.freeMk _) = _
    rw [orbitBackward_mk]
    exact mk_lift_one P n s
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change orbitForward P n (orbitBackward P n (ModuleCat.freeMk s))=ModuleCat.freeMk s
    erw [orbitBackward_mk,orbitForward_mk,lift_project]
    rfl
lemma orbit_natural {n m:SimplexCategoryᵒᵖ} (f:n⟶m) :
    (orbitIso P n.unop.len).hom ≫ (ModuleCat.free ℤ).map ((nerve (SingleObj P)).map f)=
    (Rep.coinvariantsFunctor ℤ (Q P)).map ((linear P).map f) ≫ (orbitIso P m.unop.len).hom := by
  apply Rep.coinvariantsFunctor_hom_ext
  apply ModuleCat.hom_ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (ModuleCat.free ℤ).map ((nerve (SingleObj P)).map f)
    (orbitForward P n.unop.len (Coinvariants.mk _ (MonoidAlgebra.single s 1))) =
    orbitForward P m.unop.len (Coinvariants.mk _ (Representation.linearizeMap ((simplicial P).map f)
      (MonoidAlgebra.single s 1)))
  erw [orbitForward_mk,Representation.linearizeMap_single,orbitForward_mk]
  change (ModuleCat.free ℤ).map _ (ModuleCat.freeMk _) = ModuleCat.freeMk _
  erw [ModuleCat.free_map_apply]
  rfl
end TranslationNerve

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
lemma orbit_d (m:ℕ) : (orbitIso P (m+1)).hom ≫ (FreeChains.complex (nerve (SingleObj P))).d (m+1) m =
    (Rep.coinvariantsFunctor ℤ (Q P)).map ((complex P).d (m+1) m) ≫ (orbitIso P m).hom := by
  rw [show (FreeChains.complex (nerve (SingleObj P))).d (m+1) m =
      ∑ i:Fin (m+2),(-1:ℤ)^i.val • (ModuleCat.free ℤ).map ((nerve (SingleObj P)).δ i) from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  rw [show (complex P).d (m+1) m=∑ i:Fin (m+2),(-1:ℤ)^i.val • (linear P).δ i from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  erw [Functor.map_sum,Preadditive.comp_sum,Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  erw [Functor.map_zsmul,Preadditive.comp_zsmul,Preadditive.zsmul_comp]
  exact congrArg (fun f => ((-1:ℤ)^i.val) • f) (orbit_natural P (SimplexCategory.δ i).op)
noncomputable def orbitChainIso : ((Rep.coinvariantsFunctor ℤ (Q P)).mapHomologicalComplex c).obj (complex P) ≅
    FreeChains.complex (nerve (SingleObj P)) := by
  refine HomologicalComplex.Hom.isoOfComponents (orbitIso P) ?_
  rintro n m rfl
  exact orbit_d P m
noncomputable def unitCoinvariantsIso : (Rep.coinvariantsTensor ℤ (Q P)).obj (Rep.trivial ℤ (Q P) ℤ) ≅
    Rep.coinvariantsFunctor ℤ (Q P) :=
  Functor.isoWhiskerRight (leftUnitorNatIso (Rep ℤ (Q P))) (Rep.coinvariantsFunctor ℤ (Q P)) ≪≫
    Functor.leftUnitor _

noncomputable def completionHomologyIso (n:ℕ) :
    (nerve (SingleObj P)).homology Z n ≅ groupHomology (Rep.trivial ℤ (Q P) ℤ) n := by
  classical
  let e : (resolution P).complex.coinvariantsTensorObj (Rep.trivial ℤ (Q P) ℤ) ≅
      FreeChains.complex (nerve (SingleObj P)) :=
    (NatIso.mapHomologicalComplex (unitCoinvariantsIso P) c).app (complex P) ≪≫ orbitChainIso P
  exact (HomologicalComplex.homologyFunctor A c n).mapIso (complexIso _) ≪≫
    ((HomologicalComplex.homologyFunctor A c n).mapIso e).symm ≪≫
    (groupHomologyIso (Rep.trivial ℤ (Q P) ℤ) n (resolution P)).symm
end TranslationNerve

end

end OAI
