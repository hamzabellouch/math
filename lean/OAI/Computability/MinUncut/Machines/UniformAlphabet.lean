import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformAlgebra
import OAI.Computability.MinUncut.Estimates.Bridge
import OAI.Computability.MinUncut.Search.UniformQuantifier

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
abbrev Slot (p : P) := Σj:Fin (t p),Fin (width (h p j))
def axes := fin t ht
def positions : UEncoding P (fun _=>Fin 3) := fixed (Encoding.fin 3)
def slotPairs := (axes t ht).prod (positions (P:=P))
def slotGood (p : P) (x : Fin (t p) × Fin 3) : Bool := !h p x.1 || decide (x.2=0)
omit [Primcodable P] in
lemma slotGood_iff (p : P) (x : Fin (t p) × Fin 3) :
    slotGood t h p x=true ↔ x.2.val<width (h p x.1) := by
  cases hh:h p x.1
  · simp [slotGood,hh,width,x.2.isLt]
  · simp only [slotGood,hh,Bool.not_true,Bool.false_or,decide_eq_true_eq,width,ite_true]
    constructor
    · intro hx; rw [hx]; decide
    · intro hx; apply Fin.ext; change x.2.val=0; omega
include hc in
lemma map_slotGood : (slotPairs t ht).Map bool (slotGood t h) := by
  have hh : (slotPairs t ht).Map ((axes t ht).function bool) (fun p _=>h p) := map_const hc
  exact map_or (map_not (map_apply hh (map_fst _ _)))
    (map_bool_eq (map_snd _ _) (map_const (Computable.const 0)))

def slotEquiv (p : P) : Slot t h p ≃ {x:Fin (t p) × Fin 3 // slotGood t h p x=true} where
  toFun x := ⟨(x.1,⟨x.2.val,by
    have hx:=x.2.isLt
    have hw:width (h p x.1)≤3 := by cases h p x.1 <;> decide
    omega⟩),(slotGood_iff t h p _).mpr x.2.isLt⟩
  invFun x := ⟨x.val.1,⟨x.val.2.val,(slotGood_iff t h p x.val).mp x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def slots : UEncoding P (Slot t h) :=
  ((slotPairs t ht).restrict (slotGood t h) (map_slotGood t ht h hc)).ofEquiv (slotEquiv t h)
def labelEquiv (p : P) : LocalTemplate.Alphabet (h p) ≃ (Slot t h p → F₂) where
  toFun x := fun j=>x j.1 j.2
  invFun x := fun j k=>x ⟨j,k⟩
  left_inv _ := rfl
  right_inv _ := rfl

def labels : UEncoding P (fun p=>LocalTemplate.Alphabet (h p)) :=
  ((slots t ht h hc).function (field P)).ofEquiv (labelEquiv t h)
def formsEquiv (p : P) : Forms (LocalTemplate.Alphabet (h p)) ≃ F₂ × (Slot t h p → F₂) :=
  (SampleEnumeration.formsCurryEquiv (Fin (t p)) (fun j=>Fin (width (h p j)))).trans
    (SampleEnumeration.formsPiEquiv (Slot t h p))
def forms : UEncoding P (fun p=>Forms (LocalTemplate.Alphabet (h p))) :=
  ((field P).prod ((slots t ht h hc).function (field P))).ofEquiv (formsEquiv t h)

omit [Primcodable P] in
lemma forms_apply (p : P) (f : Forms (LocalTemplate.Alphabet (h p))) (x : LocalTemplate.Alphabet (h p)) :
    f x=(formsEquiv t h p f).1+∑j:Slot t h p,(formsEquiv t h p f).2 j*labelEquiv t h p x j := by
  let e:=SampleEnumeration.formsCurryEquiv (Fin (t p)) (fun j=>Fin (width (h p j)))
  let f':=e f
  have he : f x=f' (labelEquiv t h p x) := rfl
  rw [he]
  change f' (labelEquiv t h p x)=f' 0+∑j:Slot t h p,
    (LinearEquiv.piRing F₂ F₂ (Slot t h p) F₂ f'.linear) j*labelEquiv t h p x j
  have hl := congrArg (fun L : (Slot t h p → F₂) →ₗ[F₂] F₂=>L (labelEquiv t h p x))
    ((LinearEquiv.piRing F₂ F₂ (Slot t h p) F₂).symm_apply_apply f'.linear)
  rw [LinearEquiv.piRing_symm_apply] at hl
  have hd:=congrFun f'.decomp (labelEquiv t h p x)
  change f' (labelEquiv t h p x)=f'.linear (labelEquiv t h p x)+f' 0 at hd
  rw [hd,←hl]
  simp only [smul_eq_mul,mul_comm]
  exact add_comm _ _

lemma map_forms_apply : ((forms t ht h hc).prod (labels t ht h hc)).Map (field P)
    (fun _ x=>x.1 x.2) := by
  let s:=slots t ht h hc
  let f:=forms t ht h hc
  let a:=labels t ht h hc
  let c:=f.prod a
  have hf : c.Map ((field P).prod (s.function (field P))) (fun p x=>formsEquiv t h p x.1) :=
    (map_to _ (formsEquiv t h)).first
  have ha : c.Map (s.function (field P)) (fun p x=>labelEquiv t h p x.2) :=
    (map_to _ (labelEquiv t h)).second
  have hcoef:=map_comp hf (map_snd _ _)
  have hv:=map_snd c s
  have hs:=map_field_sum (map_field_mul (map_apply hcoef.first hv) (map_apply ha.first hv))
  apply (map_field_add (map_comp hf (map_fst _ _)) hs).ofEq
  intro p x
  exact (forms_apply t h p x.1 x.2).symm
end MinUncut.Preprocess.Alphabet

end
end

end OAI
