import Mathlib
import OAI.GroupTheory.SimpleOvergroups.EnlargementEffective
import OAI.GroupTheory.SimpleOvergroups.MatrixEffective
import OAI.GroupTheory.SimpleOvergroups.EffectiveActions

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Double
open BoundedEncoding NamedAction
noncomputable section
open scoped Classical

variable {A k₀ k₁ k₂ P₁ P₂ : Type*}
  [CommRing k₀] [CommRing k₁] [CommRing k₂]
  [Primcodable A] [Primcodable k₀] [Primcodable k₁] [Primcodable k₂]
  [Finite k₀] [Finite k₁] [Finite k₂]
  [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
  {n : ℕ}

abbrev G₀ (k A : Type*) (n : ℕ) := MatrixWords.Word k A n
abbrev X₀ (k A : Type*) (n : ℕ) := MatrixWords.Point k A n
abbrev G₁ (P k A : Type*) (n : ℕ) := Enlargement.Word P (G₀ k A n)
abbrev X₁ (P k A : Type*) (n : ℕ) := Enlargement.Point P (G₀ k A n) (X₀ k A n)
abbrev G₂ (P₁ P₂ k A : Type*) (n : ℕ) := Enlargement.Word P₂ (G₁ P₁ k A n)
abbrev X₂ (P₁ P₂ k A : Type*) (n : ℕ) := Enlargement.Point P₂ (G₁ P₁ k A n) (X₁ P₁ k A n)

abbrev base (grade : List A → ℕ) := MatrixWords.nameOperations (k:=k₀) (n:=n) grade
abbrev first (grade : List A → ℕ) := Enlargement.operations (P:=P₁) (base (k₀:=k₀) (n:=n) grade)
abbrev operations (grade : List A → ℕ) :=
  Enlargement.operations (P:=P₂) (first (P₁:=P₁) (k₀:=k₀) (n:=n) grade)

variable (e₁ : P₁ → Enlargement.Coeff.Name k₁) (e₂ : P₂ → Enlargement.Coeff.Name k₂)
variable (grade : List A → ℕ) (omega : List A) (f : List A → Part (List A))

def partialGroupKey : G₂ P₁ P₂ k₀ A n → Part (ℕ × ℕ) :=
  Enlargement.partialGroupKey (first grade) e₂
    (Enlargement.partialGroupKey (base grade) e₁
      (MatrixWords.partialGroupKey (k:=k₀) (n:=n) omega f))

def partialPointKey : X₂ P₁ P₂ k₀ A n → Part ℕ :=
  Enlargement.partialPointKey (first grade) e₂
    (Enlargement.partialPointKey (base grade) e₁
      (MatrixWords.partialPointKey (k:=k₀) (n:=n) omega f))

def test (w : List (Letter (G₂ P₁ P₂ k₀ A n) (X₂ P₁ P₂ k₀ A n))) :
    Part (Result (ℕ × ℕ) ℕ) :=
  (operations grade).test (partialGroupKey e₁ e₂ grade omega f)
    (partialPointKey e₁ e₂ grade omega f) w

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
attribute [local instance] WordCalculus.rawMatrixAction

abbrev calculus := Enlargement.calculus (k:=k₂)
  (Enlargement.calculus (k:=k₁) (MatrixWords.calculus (k:=k₀) (n:=n) C))

variable (he₁ : ∀ p, Enlargement.Coeff.value (e₁ p) * Enlargement.Coeff.value (e₁ p) =
    Enlargement.Coeff.value (e₁ p))
  (he₂ : ∀ p, Enlargement.Coeff.value (e₂ p) * Enlargement.Coeff.value (e₂ p) =
    Enlargement.Coeff.value (e₂ p))

abbrev interpret₁ := Enlargement.interpretation (base (MatrixWords.grade C)) e₁
  (MatrixWords.interpretation (k:=k₀) (n:=n) C) he₁

abbrev interpretation := Enlargement.interpretation (first (MatrixWords.grade C)) e₂
  (interpret₁ (k₀:=k₀) (n:=n) e₁ C he₁) he₂

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem partialGroupKey_full {d : ℕ} (w : G₂ P₁ P₂ k₀ A n)
    (hw : (operations (MatrixWords.grade C)).gcost w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation e₁ e₂ C he₁ he₂).gkey w ∈
      partialGroupKey e₁ e₂ (MatrixWords.grade C) C.omega.toList f w := by
  apply Enlargement.partialGroupKey_full _ _ _ _ _ _ hw
  intro g hg
  apply Enlargement.partialGroupKey_full _ _ _ _ _ _ hg
  intro h hh
  exact MatrixWords.partialGroupKey_full C f h hh hf

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem partialPointKey_full {d : ℕ} (x : X₂ P₁ P₂ k₀ A n)
    (hx : (operations (MatrixWords.grade C)).xcost x ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation e₁ e₂ C he₁ he₂).xkey x ∈
      partialPointKey e₁ e₂ (MatrixWords.grade C) C.omega.toList f x := by
  apply Enlargement.partialPointKey_full _ _ _ _ _ _ hx
  intro y hy
  apply Enlargement.partialPointKey_full _ _ _ _ _ _ hy
  intro z hz
  exact MatrixWords.partialPointKey_full C f z hz hf

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem test_full {d : ℕ} (w : List (Letter (G₂ P₁ P₂ k₀ A n) (X₂ P₁ P₂ k₀ A n)))
    (hw : (operations (MatrixWords.grade C)).wordCost w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (operations (MatrixWords.grade C)).totalTest
      (interpretation e₁ e₂ C he₁ he₂).gkey (interpretation e₁ e₂ C he₁ he₂).xkey w ∈
      test e₁ e₂ (MatrixWords.grade C) C.omega.toList f w := by
  exact Operations.test_full _ _ _ _ _
    (fun g hg => partialGroupKey_full e₁ e₂ f C he₁ he₂ g hg hf)
    (fun x hx => partialPointKey_full e₁ e₂ f C he₁ he₂ x hx hf) w hw


local instance : Primcodable (G₂ P₁ P₂ k₀ A n) := inferInstance
local instance : Primcodable (X₂ P₁ P₂ k₀ A n) := inferInstance

 theorem primrec_inv_base : Primrec ((base (k₀:=k₀) (n:=n) grade).inv) := MatrixWords.primrec_inverse
omit [Finite k₀] in
 theorem primrec_act_base : Primrec₂ ((base (k₀:=k₀) (n:=n) grade).act) :=
  (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)
omit [Finite P₁] in
 theorem primrec_inv_first : Primrec ((first (P₁:=P₁) (k₀:=k₀) (n:=n) grade).inv) :=
  Enlargement.primrec_inverse _ (primrec_inv_base grade)
omit [Finite P₁] [Finite P₂] in
 theorem primrec_plan : Primrec₂ ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).plan) :=
  Enlargement.primrec_plan _ (primrec_inv_first grade)

variable {Param : Type*} [Primcodable Param] {F : Param → List A → Part (List A)}

 theorem partrec_partialGroupKey (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => partialGroupKey (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Enlargement.partrec_partialGroupKey _ e₂ Primrec.list_append (primrec_inv_first grade)
    (Enlargement.partrec_partialGroupKey _ e₁ Primrec.list_append (primrec_inv_base grade)
      (MatrixWords.partrec_partialGroupKey omega hF))

 theorem partrec_partialPointKey (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => partialPointKey (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Enlargement.partrec_partialPointKey _ e₂ Primrec.list_append (Enlargement.primrec_act _)
    (Enlargement.partrec_partialPointKey _ e₁ Primrec.list_append (primrec_act_base grade)
      (MatrixWords.partrec_partialPointKey omega hF))

 theorem partrec_test (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => test (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Operations.partrec_test _ (primrec_plan grade).to_comp
    (partrec_partialGroupKey e₁ e₂ grade omega hF) (partrec_partialPointKey e₁ e₂ grade omega hF)

omit [Finite P₁] [Finite P₂] in
 theorem primrec_gcost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).gcost) :=
  Enlargement.primrec_gcost _ (Enlargement.primrec_gcost _ (MatrixWords.primrec_gcost hg))

omit [Finite P₁] [Finite P₂] in
 theorem primrec_xcost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).xcost) :=
  Enlargement.primrec_xcost _ (Enlargement.primrec_gcost _ (MatrixWords.primrec_gcost hg))
    (Enlargement.primrec_xcost _ (MatrixWords.primrec_gcost hg) (MatrixWords.primrec_xcost hg))

omit [Finite P₁] [Finite P₂] in
 theorem primrec_cost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).letterCost) :=
  (operations grade).primrec_letterCost (primrec_gcost grade hg) (primrec_xcost grade hg)
end
end SimpleFInftyOvergroups.EffectiveNames.Double

end OAI
