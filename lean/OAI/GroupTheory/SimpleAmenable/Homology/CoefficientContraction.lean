import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.CoefficientNerve

namespace OAI

open CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology
namespace SemiExtra
variable {C:Type*} [Category* C]
structure Data (X:Augmented C) where
  s' : X.right ⟶ X.left _⦋0⦌
  s : ∀n:ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n+1⦌
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌)=𝟙 X.right
  s₀_comp_δ₁ : s 0 ≫ X.left.δ 1=X.hom.app (op ⦋0⦌) ≫ s'
  s_comp_δ₀ : ∀n:ℕ, s n ≫ X.left.δ 0=𝟙 _
  s_comp_δ : ∀ (n:ℕ) (i:Fin (n+2)),s (n+1) ≫ X.left.δ i.succ=X.left.δ i ≫ s n
attribute [reassoc] Data.s₀_comp_δ₁ Data.s_comp_δ
attribute [reassoc (attr:=simp)] Data.s'_comp_ε Data.s_comp_δ₀

noncomputable def homotopyEquiv [Preadditive C] [HasZeroObject C]
    {X:Augmented C} (ed:Data X) :
    HomotopyEquiv (AlternatingFaceMapComplex.obj (Augmented.drop.obj X))
      ((ChainComplex.single₀ C).obj (Augmented.point.obj X)) where
  hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C:=AlternatingFaceMapComplex.obj X.left)])
  homotopyHomInvId :=
    { hom i := Pi.single (i+1) (-ed.s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex,Homotopy.dNext_zero_chainComplex]
          simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C:=AlternatingFaceMapComplex.obj X.left),Data.s_comp_δ₀,Data.s₀_comp_δ₁]
        | succ i =>
          rw [Homotopy.prevD_chainComplex,Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_succ (n:=i+2),Data.s_comp_δ₀,Preadditive.sum_comp,
            Preadditive.comp_sum,Data.s_comp_δ,pow_succ] }
end SemiExtra
namespace CoefficientNerve

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable (F:C ⥤ ModuleCat.{0} R)
lemma weighted_eq {n:ℕ} {s t:Simplex C n} (h:s=t) {x:C}
    (f:x ⟶ s.right.unop) (g:x ⟶ t.right.unop)
    (w:f ≫ eqToHom (congrArg (fun s:Simplex C n => s.right.unop) h)=g) :
    F.map f ≫ single F s=F.map g ≫ single F t := by
  subst t
  simpa only [eqToHom_refl,Category.comp_id] using congrArg (fun v=>F.map v ≫ single F s) w
variable {d:C} (hd:IsTerminal d)
noncomputable def augmentation : simplicial F ⟶ (SimplicialObject.const _).obj (F.obj d) where
  app n := desc F (fun s=>F.map (hd.from s.right.unop))
  naturality n m f := by
    apply hom_ext; intro s
    change single F s ≫ map F f.unop ≫ desc F _ = single F s ≫ desc F _ ≫ 𝟙 _
    rw [single_map_assoc,single_desc,Category.comp_id,single_desc,←F.map_comp]
    congr 1
    exact hd.hom_ext _ _
noncomputable def augmented : Augmented (ModuleCat.{0} R) :=
  { left := simplicial F, right := F.obj d, hom := augmentation F hd }
noncomputable def extra (n:ℕ) : Obj F n ⟶ Obj F (n+1) :=
  desc F (fun s=>single F (NervePrefix.extra hd.op s))
@[reassoc (attr:=simp)] lemma single_extra {n:ℕ} (s:Simplex C n) :
    single F s ≫ extra F hd n=single F (NervePrefix.extra hd.op s) := single_desc _ _ _
lemma extra_zero (n:ℕ) : extra F hd n ≫ (simplicial F).δ 0=𝟙 _ := by
  apply hom_ext; intro s
  change single F s ≫ extra F hd n ≫ map F (SimplexCategory.δ 0)=single F s ≫ 𝟙 _
  erw [single_extra_assoc,single_map,Category.comp_id]
  change F.map ((s.map (𝟙 _)).unop) ≫ single F s=single F s
  simp
lemma extra_tail_map {n:ℕ} (s:Simplex C n) (i j:Fin (n+1)) (hij:i≤j)
    (k:Fin (n+2)) (hk:k=i.succ) (hkj:k≤j.succ)
    (he:((NervePrefix.extra hd.op s).obj k).unop=(s.obj i).unop) :
    ((NervePrefix.extra hd.op s).map (homOfLE hkj)).unop ≫ eqToHom he =
      (s.map (homOfLE hij)).unop := by
  subst k
  change (s.map (homOfLE hij)).unop ≫ eqToHom _ = (s.map (homOfLE hij)).unop
  simp
lemma extra_succ (n:ℕ) (i:Fin (n+2)) :
    extra F hd (n+1) ≫ (simplicial F).δ i.succ=(simplicial F).δ i ≫ extra F hd n := by
  apply hom_ext; intro s
  change single F s ≫ extra F hd (n+1) ≫ map F (SimplexCategory.δ i.succ) =
    single F s ≫ map F (SimplexCategory.δ i) ≫ extra F hd n
  erw [single_extra_assoc,single_map,single_map_assoc,single_extra]
  apply weighted_eq F (NervePrefix.precomp_delta hd.op s i)
  change ((NervePrefix.extra hd.op s).map (homOfLE
    (show i.succ.succAbove (Fin.last n).succ ≤ (Fin.last (n+1)).succ from Fin.le_last _))).unop ≫ eqToHom _ =
    (s.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))).unop
  exact extra_tail_map hd s (i.succAbove (Fin.last n)) (Fin.last (n+1)) _ _
    (Fin.succ_succAbove_succ i (Fin.last n)) _ _
noncomputable def contraction : SemiExtra.Data (augmented F hd) where
  s' := single F (ComposableArrows.mk₀ (op d))
  s := extra F hd
  s'_comp_ε := by
    change single F _ ≫ desc F _=𝟙 _
    erw [single_desc]
    change F.map (hd.from d)=𝟙 (F.obj d)
    rw [show hd.from d=𝟙 d from hd.hom_ext _ _,F.map_id]
  s₀_comp_δ₁ := by
    apply hom_ext; intro s
    change single F s ≫ extra F hd 0 ≫ map F (SimplexCategory.δ 1) =
      single F s ≫ desc F _ ≫ single F (ComposableArrows.mk₀ (op d))
    erw [single_extra_assoc,single_map,single_desc_assoc]
    have hs : trunc (SimplexCategory.δ 1) (NervePrefix.extra hd.op s) = ComposableArrows.mk₀ (op d) := ComposableArrows.ext₀ rfl
    apply weighted_eq F hs
    exact hd.hom_ext _ _
  s_comp_δ₀ := extra_zero F hd
  s_comp_δ := extra_succ F hd
noncomputable def terminalHomotopyEquiv : HomotopyEquiv (complex F)
    ((ChainComplex.single₀ (ModuleCat R)).obj (F.obj d)) :=
  SemiExtra.homotopyEquiv (contraction F hd)
end CoefficientNerve

end OAI
