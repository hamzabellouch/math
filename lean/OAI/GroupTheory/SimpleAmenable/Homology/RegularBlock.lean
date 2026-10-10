import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularCoefficientDouble
import OAI.GroupTheory.SimpleAmenable.Simplicial.MonoidNerveCoordinates

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def block {h v:ℕ} (s:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v) :
    F.obj t.right.unop ⟶ ((double F).X h).X v :=
  single F t ≫ single ((coeffComplex F).X v) s
lemma block_hom_ext {h v:ℕ} {M:A} {f g:((double F).X h).X v ⟶ M}
    (hh:∀s t,block F s t ≫ f=block F s t ≫ g) : f=g := by
  apply CoefficientNerve.hom_ext
  intro s
  apply CoefficientNerve.hom_ext
  intro t
  exact (Category.assoc _ _ _).symm.trans ((hh s t).trans (Category.assoc _ _ _))
noncomputable def blockDesc {h v:ℕ} {M:A}
    (f:∀(_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M) :
    ((double F).X h).X v ⟶ M :=
  CoefficientNerve.desc ((coeffComplex F).X v) (fun s=>CoefficientNerve.desc F (f s))
@[reassoc (attr:=simp)] lemma block_desc {h v:ℕ} {M:A}
    (f:∀(_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M) (s) (t) :
    block F s t ≫ blockDesc F f=f s t := by
  dsimp only [block,blockDesc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => CoefficientNerve.single F t ≫ g)
      (CoefficientNerve.single_desc ((coeffComplex F).X v)
        (fun s => CoefficientNerve.desc F (f s)) s)).trans
      (CoefficientNerve.single_desc F (f s) t))
noncomputable def totalBlock {h v n:ℕ} (hn:h+v=n)
    (s:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v) :
    F.obj t.right.unop ⟶ ((double F).total c).X n :=
  block F s t ≫ (double F).ιTotal c h v n hn
lemma totalBlock_hom_ext {n:ℕ} {M:A} {f g:((double F).total c).X n ⟶ M}
    (hh:∀h v (hn:h+v=n) s t,totalBlock F hn s t ≫ f=totalBlock F hn s t ≫ g) : f=g := by
  apply HomologicalComplex₂.total.hom_ext
  intro h v hn
  apply block_hom_ext
  intro s t
  exact (Category.assoc _ _ _).symm.trans ((hh h v hn s t).trans (Category.assoc _ _ _))
noncomputable def totalBlockDesc {n:ℕ} {M:A}
    (f:∀h v (_:h+v=n) (_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M) :
    ((double F).total c).X n ⟶ M :=
  (double F).totalDesc (fun h v hn=>blockDesc F (f h v hn))
@[reassoc (attr:=simp)] lemma totalBlock_desc {n:ℕ} {M:A}
    (f:∀h v (_:h+v=n) (_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M)
    (h v:ℕ) (hn:h+v=n) (s) (t) :
    totalBlock F hn s t ≫ totalBlockDesc F f=f h v hn s t := by
  dsimp only [totalBlock,totalBlockDesc]
  rw [Category.assoc,HomologicalComplex₂.ι_totalDesc,block_desc]
end RegularCoefficient

namespace RegularLabels
open FreeChains CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
abbrev W (h v:ℕ) := (Fin v→P) × P × (Fin h→P)
abbrev fiber (p:P) : A := F.obj (ActionCategory.objEquiv P P p)
lemma rightEq {v:ℕ} (p:P) (y:Fin v→P) :
    (lift p (ofLabels y)).right.unop = ActionCategory.objEquiv P P p := by
  apply (ActionCategory.objEquiv P P).symm.injective
  exact lift_right p (ofLabels y)
noncomputable def inj {h v:ℕ} (w:W (P:=P) h v) :
    fiber F w.2.1 ⟶ ((RegularCoefficient.double F).X h).X v :=
  eqToHom (congrArg F.obj (rightEq w.2.1 w.1).symm) ≫
    RegularCoefficient.block F (ofLabels w.2.2) (lift w.2.1 (ofLabels w.1))
noncomputable def desc {h v:ℕ} {M:A} (f:∀w:W (P:=P) h v,fiber F w.2.1 ⟶ M) :
    ((RegularCoefficient.double F).X h).X v ⟶ M :=
  RegularCoefficient.blockDesc F (fun s t=> f (labels (t ⋙ (ActionCategory.π P P).op),t.right.unop.back,labels s))
@[reassoc (attr:=simp)] lemma include_desc {h v:ℕ} {M:A}
    (f:∀w:W (P:=P) h v,fiber F w.2.1 ⟶ M) (w:W (P:=P) h v) :
    inj F w ≫ desc F f=f w := by
  dsimp only [inj,desc]
  erw [Category.assoc,RegularCoefficient.block_desc]
  have hr:=lift_right w.2.1 (ofLabels w.1)
  change eqToHom (congrArg (fiber F) hr.symm) ≫
    f (labels (lift w.2.1 (ofLabels w.1) ⋙ (ActionCategory.π P P).op),
      (lift w.2.1 (ofLabels w.1)).right.unop.back,labels (ofLabels w.2.2)) = f w
  rw [lift_project,labels_ofLabels,labels_ofLabels]
  generalize (lift w.2.1 (ofLabels w.1)).right.unop.back = p at *
  cases hr
  simp
lemma hom_ext {h v:ℕ} {M:A} {f g:((RegularCoefficient.double F).X h).X v ⟶ M}
    (hh:∀w:W (P:=P) h v,inj F w ≫ f=inj F w ≫ g) : f=g := by
  apply RegularCoefficient.block_hom_ext
  intro s t
  obtain ⟨x,rfl⟩ := (MonoidNerveCoordinates.equiv P h).symm.surjective s
  obtain ⟨⟨p,y⟩,rfl⟩ := (RegularCoordinates.coordinates v).symm.surjective t
  obtain ⟨z,rfl⟩ := (MonoidNerveCoordinates.equiv P v).symm.surjective y
  change RegularCoefficient.block F (ofLabels x) (lift p (ofLabels z)) ≫ f =
    RegularCoefficient.block F (ofLabels x) (lift p (ofLabels z)) ≫ g
  exact (cancel_epi (eqToHom (congrArg F.obj (rightEq p z).symm))).mp
    (by simpa only [inj,Category.assoc] using hh (z,p,x))
noncomputable def isColimit (h v:ℕ) : IsColimit (Cofan.mk _ (inj F (h:=h) (v:=v))) :=
  Cofan.IsColimit.mk _ (fun s=>desc F s.inj) (fun _ _=>include_desc F _ _)
    (fun s _ hh=>hom_ext F (fun w=>(hh w).trans (include_desc F s.inj w).symm))
end RegularLabels

end

namespace MarkedCoordinates
variable {P:Type} {n:ℕ}
abbrev Split (P:Type) (n:ℕ) := Σi:Fin (n+1),(Fin i.val→P) × P × (Fin (n-i.val)→P)
def word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) : Fin (n+1)→P :=
  fun j=>if h:j.val < i.val then y ⟨j.val,h⟩ else
    if h':j.val = i.val then p else x ⟨n-j.val,by omega⟩
@[simp] lemma word_center (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    word i y p x i=p := by simp [word]
lemma word_left (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) (j:Fin i.val) :
    word i y p x ⟨j.val,by omega⟩=y j := by simp [word,j.isLt]
lemma word_right (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) (j:Fin (n-i.val)) :
    word i y p x ⟨n-j.val,by omega⟩=x j := by
  simp only [word,dite_eq_right (show ¬n-j.val < i.val from by omega),dite_eq_right (show ¬n-j.val = i.val from by omega)]
  congr 1
  apply Fin.ext
  dsimp
  omega
def vertical (w:Fin (n+1)→P) (i:Fin (n+1)) : Fin i.val→P := fun j=>w ⟨j.val,by omega⟩
def horizontal (w:Fin (n+1)→P) (i:Fin (n+1)) : Fin (n-i.val)→P := fun j=>w ⟨n-j.val,by omega⟩
lemma word_recover (w:Fin (n+1)→P) (i:Fin (n+1)) : word i (vertical w i) (w i) (horizontal w i)=w := by
  funext j
  dsimp only [word]
  split_ifs with h h'
  · rfl
  · congr 1; exact Fin.ext h'.symm
  · dsimp only [horizontal]
    congr 1
    apply Fin.ext
    dsimp
    omega
lemma vertical_word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    vertical (word i y p x) i=y := by funext j; exact word_left i y p x j
lemma horizontal_word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    horizontal (word i y p x) i=x := by funext j; exact word_right i y p x j
noncomputable def equiv (P:Type) (n:ℕ) : Split P n ≃ (Σ_:Fin (n+1),(Fin (n+1)→P)) where
  toFun s := ⟨s.1,word s.1 s.2.1 s.2.2.1 s.2.2.2⟩
  invFun s := ⟨s.1,vertical s.2 s.1,s.2 s.1,horizontal s.2 s.1⟩
  left_inv := by rintro ⟨i,y,p,x⟩; simp only [vertical_word,word_center,horizontal_word]
  right_inv := by rintro ⟨i,w⟩; simp only [word_recover]
end MarkedCoordinates

end OAI
