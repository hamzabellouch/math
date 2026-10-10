import Mathlib

namespace OAI

section
open CategoryTheory Limits Simplicial Opposite Classical
open scoped DirectSum
namespace CoefficientNerve

variable {R:Type} [CommRing R]
variable {C D E:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (F:C ⥤ ModuleCat.{0} R)
abbrev Simplex (C:Type) [Category.{0} C] (n:ℕ) := ComposableArrows Cᵒᵖ n
abbrev Coeff (n:ℕ) (s:Simplex C n) := F.obj s.right.unop
noncomputable abbrev Obj (n:ℕ) := ModuleCat.of R (⨁ (s:Simplex C n), Coeff F n s)
noncomputable def single {n:ℕ} (s:Simplex C n) : Coeff F n s ⟶ Obj F n :=
  ModuleCat.ofHom (DirectSum.lof R (Simplex C n) (fun t => (Coeff F n t : Type)) s)
noncomputable def desc {n:ℕ} {M:ModuleCat.{0} R} (f:∀s:Simplex C n, Coeff F n s ⟶ M) : Obj F n ⟶ M :=
  ModuleCat.ofHom (DirectSum.toModule R (Simplex C n) (M:=fun s => (Coeff F n s : Type)) M (fun s=>(f s).hom))
@[reassoc (attr:=simp)] lemma single_desc {n:ℕ} {M:ModuleCat.{0} R}
    (f:∀s:Simplex C n, Coeff F n s ⟶ M) (s:Simplex C n) :
    single F s ≫ desc F f=f s := by
  ext x
  exact DirectSum.toModule_lof R (φ:=fun s => (f s).hom) s x
lemma hom_ext {n:ℕ} {M:ModuleCat.{0} R} {f g:Obj F n ⟶ M}
    (h:∀s, single F s ≫ f=single F s ≫ g) : f=g := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext (R:=R) (M:=fun s:Simplex C n => (Coeff F n s : Type))
  intro s
  exact congrArg ModuleCat.Hom.hom (h s)
def trunc {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) : Simplex C m :=
  (SimplexCategory.toCat.map f).toFunctor ⋙ s
def tail {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    s.right.unop ⟶ (trunc f s).right.unop :=
  (s.map (homOfLE (Fin.le_last (f.toOrderHom (Fin.last m))))).unop
noncomputable def map {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) : Obj F n ⟶ Obj F m :=
  desc F (fun s=>F.map (tail f s) ≫ single F (trunc f s))
@[reassoc (attr:=simp)] lemma single_map {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    single F s ≫ map F f=F.map (tail f s) ≫ single F (trunc f s) := single_desc _ _ _
@[simp] lemma trunc_id {n:ℕ} (s:Simplex C n) : trunc (𝟙 ⦋n⦌) s=s := rfl
@[simp] lemma tail_id {n:ℕ} (s:Simplex C n) : tail (𝟙 ⦋n⦌) s=𝟙 _ := by
  change (s.map (𝟙 _)).unop=𝟙 _
  rw [s.map_id]; rfl
lemma trunc_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    trunc (f ≫ g) s=trunc f (trunc g s) := rfl
lemma tail_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    tail (f ≫ g) s=tail g s ≫ tail f (trunc g s) := by
  change (s.map (homOfLE (Fin.le_last (g.toOrderHom (f.toOrderHom (Fin.last l)))))).unop =
    (s.map (homOfLE (Fin.le_last (g.toOrderHom (Fin.last m))))).unop ≫
    (s.map (homOfLE (g.toOrderHom.monotone (Fin.le_last (f.toOrderHom (Fin.last l)))))).unop
  rw [←unop_comp,←s.map_comp]
  congr 2
lemma map_id (n:ℕ) : map F (𝟙 ⦋n⦌)=𝟙 _ := by
  apply hom_ext; intro s
  simp
lemma map_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) :
    map F (f ≫ g)=map F g ≫ map F f := by
  apply hom_ext; intro s
  simp only [single_map,tail_comp,F.map_comp,Category.assoc,single_map_assoc,trunc_comp]
noncomputable def simplicial : SimplicialObject (ModuleCat.{0} R) where
  obj n := Obj F n.unop.len
  map f := map F f.unop
  map_id n := map_id F n.unop.len
  map_comp f g := map_comp F g.unop f.unop
noncomputable def complex : ChainComplex (ModuleCat.{0} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} R)).obj (simplicial F)
noncomputable def post (u:C ⥤ D) (G:D ⥤ ModuleCat.{0} R) :
    simplicial (u ⋙ G) ⟶ simplicial G where
  app n := desc (u ⋙ G) (fun s=>single G (s ⋙ u.op))
  naturality n m f := by
    apply hom_ext; intro s
    simp only [simplicial,single_desc,single_map_assoc,single_map,single_desc_assoc]
    rfl
@[reassoc (attr:=simp)] lemma single_post (u:C ⥤ D) (G:D ⥤ ModuleCat.{0} R) (n:ℕ)
    (s:Simplex C n) : single (u ⋙ G) s ≫ (post u G).app (op ⦋n⦌)=single G (s ⋙ u.op) :=
  single_desc _ _ _
lemma post_id : post (𝟭 C) F=𝟙 (simplicial F) := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single (𝟭 C ⋙ F) s ≫ desc (𝟭 C ⋙ F) (fun simplex=>single F (simplex ⋙ (𝟭 C).op)) =
    single (𝟭 C ⋙ F) s ≫ 𝟙 (Obj F n.unop.len)
  rw [single_desc]
  change single F s = single F s ≫ 𝟙 (Obj F n.unop.len)
  exact (Category.comp_id _).symm
lemma post_comp (u:C ⥤ D) (v:D ⥤ E) (G:E ⥤ ModuleCat.{0} R) :
    post (u ⋙ v) G=post u (v ⋙ G) ≫ post v G := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single (u ⋙ (v ⋙ G)) s ≫ desc (u ⋙ (v ⋙ G)) (fun t=>single G (t ⋙ (u ⋙ v).op)) =
    single (u ⋙ (v ⋙ G)) s ≫ desc (u ⋙ (v ⋙ G)) (fun t=>single (v ⋙ G) (t ⋙ u.op)) ≫
    desc (v ⋙ G) (fun t=>single G (t ⋙ v.op))
  rw [single_desc,single_desc_assoc,single_desc]
  rfl
end CoefficientNerve

end

section
open CategoryTheory Limits Simplicial Opposite
namespace NervePrefix

variable {C:Type} [Category.{0} C] {d:C} (hd:IsInitial d)
def extra {n:ℕ} (s:ComposableArrows C n) : ComposableArrows C (n+1) :=
  s.precomp (hd.to s.left)
lemma zero {n:ℕ} (s:ComposableArrows C n) : (nerve C).δ 0 (extra hd s)=s := rfl
lemma obj_zero {n:ℕ} (s:ComposableArrows C n) : (extra hd s).obj 0=d := rfl
lemma succ_obj {n:ℕ} (s:ComposableArrows C n) (i:Fin (n+1)) :
    (extra hd s).obj i.succ=s.obj i := rfl
lemma precomp_delta {n:ℕ} (s:ComposableArrows C (n+1)) (i:Fin (n+2)) :
    (nerve C).δ i.succ (extra hd s)=extra hd ((nerve C).δ i s) := by
  have h₀ : ((nerve C).δ i.succ (extra hd s)).obj 0=d := by
    change (extra hd s).obj (i.succ.succAbove 0)=d
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp)]
    rfl
  have h : ((nerve C).δ i.succ (extra hd s)).δ₀=((nerve C).δ i s) := by
    have h:=congrArg (fun f => f (extra hd s)) ((nerve C).δ_comp_δ (Fin.zero_le i))
    exact h
  exact ComposableArrows.ext_succ h₀ h
    ((IsInitial.ofIso hd (eqToIso h₀.symm)).hom_ext _ _)

end NervePrefix

end

end OAI
