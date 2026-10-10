import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.CoefficientFiltered

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def zeroπ : K.X 0 ⟶ K.homology 0 := K.pOpcycles 0 ≫ K.isoHomologyι₀.inv
instance : Epi (zeroπ K) := by dsimp [zeroπ]; infer_instance
@[reassoc (attr:=simp)] lemma d_zeroπ : K.d 1 0 ≫ zeroπ K=0 := by simp [zeroπ]
noncomputable def zeroDesc {V:ModuleCat.{0} R} (f:K.X 0 ⟶ V) (hf:K.d 1 0 ≫ f=0) :
    K.homology 0 ⟶ V := K.isoHomologyι₀.hom ≫ K.descOpcycles f 1 ((ComplexShape.down ℕ).prev_eq' rfl) hf
@[reassoc (attr:=simp)] lemma zeroπ_desc {V:ModuleCat.{0} R} (f:K.X 0 ⟶ V) (hf:K.d 1 0 ≫ f=0) :
    zeroπ K ≫ zeroDesc K f hf=f := by simp [zeroπ,zeroDesc]
end ChainComplex
namespace CoefficientNerve

variable {C:Type} [Category.{0} C] (F:C ⥤ ModuleCat.{0} ℤ)
noncomputable def point (x:C) : F.obj x ⟶ Obj F 0 := single F (ComposableArrows.mk₀ (op x))
noncomputable def zeroι (x:C) : F.obj x ⟶ (complex F).homology 0 :=
  single F (ComposableArrows.mk₀ (op x)) ≫ (_root_.OAI.ChainComplex.zeroπ (complex F))
lemma d10 : (complex F).d 1 0=map F (SimplexCategory.δ 0)-map F (SimplexCategory.δ 1) := by
  change (∑ i:Fin 2, (-1:ℤ)^i.val • map F (SimplexCategory.δ i))=_
  simp [Fin.sum_univ_two]
  exact (sub_eq_add_neg _ _).symm
noncomputable def edge (s:Simplex C 1) : s.right.unop ⟶ s.left.unop :=
  (s.map (homOfLE (Fin.zero_le (Fin.last 1)))).unop
lemma single_d10 (s:Simplex C 1) :
    single F s ≫ (complex F).d 1 0 =
      point F s.right.unop-
        F.map (edge s) ≫
          point F s.left.unop := by
  dsimp only [point]
  erw [d10,Preadditive.comp_sub,single_map,single_map]
  have h0 : trunc (SimplexCategory.δ (0:Fin 2)) s=ComposableArrows.mk₀ s.right :=
    ComposableArrows.ext₀ rfl
  have h1 : trunc (SimplexCategory.δ (1:Fin 2)) s=ComposableArrows.mk₀ s.left :=
    ComposableArrows.ext₀ rfl
  have t0 : tail (SimplexCategory.δ (0:Fin 2)) s=𝟙 _ := by
    change (s.map (𝟙 _)).unop=𝟙 _
    rw [s.map_id]; rfl
  erw [t0,F.map_id,Category.id_comp]
  have e0:=single_eq F h0 rfl
  have e1:=single_eq F h1 rfl
  erw [eqToHom_refl,Category.id_comp] at e0 e1
  rw [e0,e1]
  rfl
lemma zeroι_naturality {x y:C} (f:x⟶y) : F.map f ≫ zeroι F y=zeroι F x := by
  have h:=congrArg (fun k=>single F (ComposableArrows.mk₁ f.op) ≫ k) (ChainComplex.d_zeroπ (complex F))
  erw [←Category.assoc,single_d10,Preadditive.sub_comp,comp_zero] at h
  change zeroι F x - F.map f ≫ zeroι F y=0 at h
  exact (sub_eq_zero.mp h).symm
noncomputable def zeroCocone : Cocone F where
  pt := (complex F).homology 0
  ι := { app := zeroι F
         naturality x y f := by simpa using zeroι_naturality F f }
lemma desc_d10 (d:Cocone F) : (complex F).d 1 0 ≫ desc F (fun s=>d.ι.app s.right.unop)=0 := by
  apply hom_ext; intro s
  erw [←Category.assoc,single_d10,Preadditive.sub_comp]
  dsimp only [point]
  erw [single_desc,Category.assoc,single_desc,comp_zero]
  exact sub_eq_zero.mpr (d.w (s.map (homOfLE (Fin.zero_le (Fin.last 1)))).unop).symm
noncomputable def zeroIsColimit : IsColimit (zeroCocone F) where
  desc d := _root_.OAI.ChainComplex.zeroDesc (complex F) (desc F (fun s=>d.ι.app s.right.unop)) (desc_d10 F d)
  fac d x := by
    dsimp only [zeroCocone,zeroι]
    erw [Category.assoc,ChainComplex.zeroπ_desc,single_desc]
    rfl
  uniq d m hm := by
    change (complex F).homology 0 ⟶ d.pt at m
    apply (cancel_epi (_root_.OAI.ChainComplex.zeroπ (complex F))).mp
    erw [ChainComplex.zeroπ_desc]
    apply hom_ext; intro s
    rw [single_desc]
    have he : single F s = single F (ComposableArrows.mk₀ s.right) := by
      have single_equality :=
        single_eq F (ComposableArrows.ext₀ (F:=s) (G:=ComposableArrows.mk₀ s.right) rfl) rfl
      erw [eqToHom_refl,Category.id_comp] at single_equality
      exact single_equality
    rw [he]
    exact hm s.right.unop
noncomputable def zeroIso : (complex F).homology 0 ≅ colimit F :=
  (zeroIsColimit F).coconePointUniqueUpToIso (colimit.isColimit F)
end CoefficientNerve

end

end OAI
