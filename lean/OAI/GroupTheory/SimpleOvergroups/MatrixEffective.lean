import Mathlib
import OAI.GroupTheory.SimpleOvergroups.MatrixWords
import OAI.GroupTheory.SimpleOvergroups.Rekey

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WithBound
 theorem ext' {A K : Type*} {B : KeyBall A K} {a b : WithBound B}
    (hv : a.val = b.val) (hc : a.cost = b.cost) : a = b := by
  cases a; cases b; cases hv; cases hc; rfl
end SimpleFInftyOvergroups.BoundedEncoding.WithBound

namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n m : ℕ}
variable [Primcodable A] [Primcodable k] [Finite k]
attribute [local instance] WordCalculus.rawMatrixAction

def pairedKey (x : Matrix (Fin n) (Fin n) (Raw k A) × Matrix (Fin n) (Fin n) (Raw k A)) :=
  (matrixKey x.1,matrixKey x.2)

omit [Finite k] in
 theorem pairedKey_injective [Finite k] : Function.Injective (pairedKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  exact Prod.ext (matrixKey_injective (congrArg Prod.fst h))
    (matrixKey_injective (congrArg Prod.snd h))

def calculus (C : WordCalculus (FreeMonoid A) m) :=
  (C.matrixActionCalculus k (Fin n)).rekey pairedKey columnKey pairedKey_injective columnKey_injective

def groupLabel (C : WordCalculus (FreeMonoid A) m) (w : Word k A n) : (calculus (n:=n) (k:=k) C).GLabel :=
  ⟨groupValue w,gcost (grade C) w,groupValue_mem C w⟩

def pointLabel (C : WordCalculus (FreeMonoid A) m) (x : Point k A n) : (calculus (n:=n) (k:=k) C).XLabel :=
  ⟨pointValue x,xcost (grade C) x,pointValue_mem C x⟩

def interpretation (C : WordCalculus (FreeMonoid A) m) :
    NamedAction.Interpretation (nameOperations (n:=n) (k:=k) (grade C)) (calculus (k:=k) (n:=n) C) where
  group := groupLabel C
  point := pointLabel C
  group_cost w := rfl
  point_cost x := rfl
  one := WithBound.ext' groupValue_nil rfl
  mul a b := WithBound.ext' (groupValue_append a b) (gcost_append _ a b)
  inv w := WithBound.ext' (groupValue_inverse w) (gcost_inverse _ w)
  act g x := WithBound.ext' (pointValue_act g x)
    (by change gcost _ (g++x.1) + columnCost _ x.2 = gcost _ g + xcost _ x
        simp [gcost_append,xcost,Nat.add_assoc])

def partialGroupKey (omega : List A) (f : List A → Part (List A)) (w : Word k A n) :
    Part ((Fin n → Fin n → ℕ) × (Fin n → Fin n → ℕ)) :=
  (partialMatrixKey omega f (matrix w)).bind fun a =>
    (partialMatrixKey omega f (matrix (inverse w))).map (fun b => (a,b))

def partialPointKey (omega : List A) (f : List A → Part (List A)) (x : Point k A n) :
    Part (Fin n → ℕ) := partialColumnKey omega f (column x)

 theorem partialGroupKey_full (C : WordCalculus (FreeMonoid A) m)
    (f : List A → Part (List A)) (w : Word k A n) {d : ℕ}
    (hw : gcost (grade C) w ≤ d)
    (h : ∀ u, grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation (k:=k) (n:=n) C).gkey w ∈ partialGroupKey C.omega.toList f w := by
  have hp := partialMatrixKey_full C f (matrix w)
    ((cost_matrix (grade C) (grade_nil C) (grade_append C) w).trans hw) h
  have hi := partialMatrixKey_full C f (matrix (inverse w))
    ((cost_matrix (grade C) (grade_nil C) (grade_append C) (inverse w)).trans (by simpa using hw)) h
  change (matrixKey (C.matrixCollect k (groupValue w).val),
    matrixKey (C.matrixCollect k (groupValue w).inv)) ∈ _
  simp only [value_matrix,groupValue_inverse] at hp hi
  exact Part.mem_bind_iff.mpr ⟨_,hp,Part.mem_map _ hi⟩

 theorem partialPointKey_full (C : WordCalculus (FreeMonoid A) m)
    (f : List A → Part (List A)) (x : Point k A n) {d : ℕ}
    (hx : xcost (grade C) x ≤ d)
    (h : ∀ u, grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation (k:=k) (n:=n) C).xkey x ∈ partialPointKey C.omega.toList f x := by
  have hh := partialColumnKey_full C f (column x)
    ((cost_column (grade C) (grade_nil C) (grade_append C) x).trans hx) h
  change columnKey (C.columnCollect k (pointValue x)) ∈ partialColumnKey C.omega.toList f (column x)
  simpa only [value_column] using hh

 theorem primrec_rootInv : Primrec (rootInv (k:=k) (A:=A) (n:=n)) :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    (Polynomial.primrec_negate.comp (Primrec.snd.comp Primrec.snd)))

 theorem primrec_inverse : Primrec (inverse (k:=k) (A:=A) (n:=n)) :=
  Primrec.list_map Primrec.list_reverse (primrec_rootInv.comp Primrec.snd).to₂

omit [Finite k] in
 theorem primrec_rootMatrix [Finite k] : Primrec (rootMatrix (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  apply Finite.primrec_function
  intro j
  have ht : PrimrecPred (fun r : Root k A n => r.1 ≠ r.2.1 ∧ r.1=i ∧ r.2.1=j) :=
    ((Primrec.dom_finite fun p : Fin n × Fin n => decide (p.1 ≠ p.2 ∧ p.1=i ∧ p.2=j)).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))).primrecPred
  exact Primrec.list_append.comp (Primrec.const (oneName i j))
    (Primrec.ite ht (Primrec.snd.comp Primrec.snd) (Primrec.const []))

 theorem primrec_matrix : Primrec (matrix (k:=k) (A:=A) (n:=n)) :=
  Primrec.list_foldr Primrec.id (Primrec.const oneName)
    (MatrixNames.primrec_product.comp (primrec_rootMatrix.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_column : Primrec (column (k:=k) (A:=A) (n:=n)) :=
  primrec_mulVec.comp (primrec_matrix.comp Primrec.fst) Primrec.snd

omit [CommRing k] [Finite k] in
 theorem primrec_gcost [CommRing k] [Finite k] {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (gcost (k:=k) (n:=n) grade) := by
  have hs : Primrec (fun l : List ℕ => l.sum) :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact hs.comp (Primrec.list_map Primrec.id
    ((Polynomial.primrec_cost hg).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)

 theorem primrec_xcost {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (xcost (k:=k) (n:=n) grade) :=
  Primrec.nat_add.comp ((primrec_gcost hg).comp Primrec.fst)
    ((primrec_columnCost hg).comp Primrec.snd)

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
 theorem partrec_partialGroupKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialGroupKey (k:=k) (n:=n) omega (f p)) := by
  have hp : Partrec (fun p : P × Word k A n => partialMatrixKey omega (f p.1) (matrix p.2)) :=
    (partrec_partialMatrixKey omega hf).comp Computable.fst (primrec_matrix.to_comp.comp Computable.snd)
  apply hp.bind
  have hi : Partrec (fun p : (P × Word k A n) × (Fin n → Fin n → ℕ) =>
      partialMatrixKey omega (f p.1.1) (matrix (inverse p.1.2))) :=
    (partrec_partialMatrixKey omega hf).comp (Computable.fst.comp Computable.fst)
      (primrec_matrix.to_comp.comp (primrec_inverse.to_comp.comp (Computable.snd.comp Computable.fst)))
  exact (hi.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂

 theorem partrec_partialPointKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialPointKey (k:=k) (n:=n) omega (f p)) :=
  (partrec_partialColumnKey omega hf).comp Computable.fst (primrec_column.to_comp.comp Computable.snd)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
