import Mathlib
import OAI.GroupTheory.SimpleOvergroups.EffectiveArrays
import OAI.GroupTheory.SimpleOvergroups.EnlargementNames
import OAI.GroupTheory.SimpleOvergroups.MatrixEffective
import OAI.GroupTheory.SimpleOvergroups.PlanEffective

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
open BinaryPrefixOperators.Arithmetic
noncomputable section
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)
  (e : P → Coeff.Name k)
variable [Primcodable k]

def arrayKey {J : Type*} [Primcodable J] : (J →₀ D k) → ℕ :=
  semanticKey (Array.value Coeff.value id)
    (Array.value_surjective Coeff.value id Lists.value_surjective Function.surjective_id)

 theorem arrayKey_injective {J : Type*} [Primcodable J] :
    Function.Injective (arrayKey (k:=k) (J:=J)) := semanticKey_injective _ _

def pairedKey {J : Type*} [Primcodable J] (p : (J →₀ D k) × (J →₀ D k)) : ℕ × ℕ :=
  (arrayKey p.1,arrayKey p.2)

 theorem pairedKey_injective {J : Type*} [Primcodable J] :
    Function.Injective (pairedKey (k:=k) (J:=J)) := by
  intro p q h
  exact Prod.ext (arrayKey_injective (congrArg Prod.fst h)) (arrayKey_injective (congrArg Prod.snd h))

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  (C : ActionCalculus V Y K L m) [Primcodable K] [Primcodable L]

def calculus : ActionCalculus (MonoidAlgebra (D k) V)ˣ (Y →₀ D k) (ℕ × ℕ) ℕ m :=
  (C.enlargement (D k)).rekey pairedKey arrayKey pairedKey_injective arrayKey_injective

variable {C} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

def groupLabel (w : Word P G) : (calculus (k:=k) C).GLabel :=
  ⟨groupValue N e I he w,gcost N w,group_mem N e I he w⟩
def pointLabel (x : Point P G X) : (calculus (k:=k) C).XLabel :=
  ⟨pointValue N e I he x,xcost N x,point_mem N e I he x⟩

def interpretation : Interpretation (operations (P:=P) N) (calculus (k:=k) C) where
  group := groupLabel N e I he
  point := pointLabel N e I he
  group_cost w := rfl
  point_cost x := rfl
  one := WithBound.ext' (groupValue_nil N e I he) rfl
  mul a b := WithBound.ext' (groupValue_append N e I he a b) (gcost_append N a b)
  inv w := WithBound.ext' (groupValue_inverse N e I he w) (gcost_inverse N w)
  act g x := WithBound.ext' (pointValue_act N e I he g x)
    (by change gcost N (g++x.1) + N.xcost x.2 = gcost N g + xcost N x
        simp [xcost,Nat.add_assoc])

variable [Primcodable G] [Primcodable X]

def partialGroupKey (f : G → Part K) (w : Word P G) : Part (ℕ × ℕ) :=
  (Array.collectedKey Coeff.value f (array N e w)).bind fun a =>
    (Array.collectedKey Coeff.value f (array N e (inverse N w))).map fun b => (a,b)

def partialPointKey (f : X → Part L) (x : Point P G X) : Part ℕ :=
  Array.collectedKey Coeff.value f (pointArray N e x)

omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : Word P G) {d : ℕ}
    (hw : gcost N w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N e I he).gkey w ∈ partialGroupKey N e f w := by
  have h (u : Word P G) (hu : gcost N u ≤ d) :=
    Array.collectedKey_full Coeff.value Lists.value_surjective f
      (fun g => (I.group g).val) C.group.key (array N e u)
      (fun a ha => hf a.2 ((array_bound N e u a ha).trans hu))
  have h' (u : Word P G) (hu : gcost N u ≤ d) :
      arrayKey (C.group.algebraCollect (D k) (groupValue N e I he u).val) ∈
        Array.collectedKey Coeff.value f (array N e u) := by
    have hh := h u hu
    have hv := congrArg MonoidAlgebra.coeff (value_array N e I he u)
    change Array.value Coeff.value (fun g => (I.group g).val) (array N e u) = _ at hv
    rw [hv] at hh
    exact hh
  change (arrayKey (C.group.algebraCollect (D k) (groupValue N e I he w).val),
    arrayKey (C.group.algebraCollect (D k) (groupValue N e I he w).inv)) ∈ _
  exact Part.mem_bind_iff.mpr ⟨_,h' w hw,Part.mem_map _ (by
    have hh := h' (inverse N w) (by simpa using hw)
    simpa only [groupValue_inverse, ← Units.inv_eq_val_inv] using hh)⟩

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : Point P G X) {d : ℕ}
    (hx : xcost N x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N e I he).xkey x ∈ partialPointKey N e f x := by
  have h := Array.collectedKey_full Coeff.value Lists.value_surjective f
    (fun y => (I.point y).val) C.point.key (pointArray N e x)
    (fun a ha => hf a.2 ((pointArray_bound N e x a ha).trans hx))
  rw [value_pointArray N e I he] at h
  exact h

variable [Primcodable P] [Finite P] [Finite k]

 theorem computable_array_eq {J : Type*} [Primcodable J] : ComputablePred
    (fun p : Array.Name (Coeff.Name k) J × Array.Name (Coeff.Name k) J =>
      Array.value Coeff.value id p.1 = Array.value Coeff.value id p.2) := by
  apply Array.computable_value_eq Coeff.value id [] (·++·) Primrec.list_append
    (show ComputablePred (fun p : J × J => p.1 = p.2) from Primrec.eq.computablePred)
    Lists.computable_value_eq
  · exact Lists.value_nil
  · exact Lists.value_append

omit [Primcodable X] [Finite P] in
 theorem primrec_inverse (hi : Primrec N.inv) : Primrec (inverse (P:=P) N) :=
  Primrec.list_map Primrec.list_reverse
    ((Primrec.fst.comp Primrec.snd).pair (hi.comp (Primrec.snd.comp Primrec.snd))).to₂

omit [Finite P] in
 theorem primrec_act : Primrec₂ ((operations (P:=P) N).act) :=
  (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)

omit [Finite P] in
 theorem primrec_plan (hi : Primrec N.inv) : Primrec₂ ((operations (P:=P) N).plan) :=
  (operations N).primrec_plan Primrec.list_append (primrec_inverse N hi) (primrec_act N)

omit [Primcodable X] in
 theorem primrec_rootArray : Primrec (rootArray N e) := by
  have hc : Primrec (Coeff.complement (k:=k)) :=
    Primrec.list_append.comp (Primrec.const Coeff.one) Lists.primrec_negate
  have he : Primrec e := Primrec.dom_finite e
  exact Primrec.list_cons.comp
    ((hc.comp (he.comp Primrec.fst)).pair (Primrec.const N.one))
    (Primrec.list_cons.comp ((he.comp Primrec.fst).pair Primrec.snd) (Primrec.const []))

omit [Primcodable X] in
 theorem primrec_array (hm : Primrec₂ N.mul) : Primrec (array N e) :=
  Primrec.list_foldr Primrec.id (Primrec.const [(Coeff.one,N.one)])
    ((Array.primrec_product Lists.primrec_product hm).comp
      ((primrec_rootArray N e).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_pointArray (hm : Primrec₂ N.mul) (hx : Primrec₂ N.act) :
    Primrec (pointArray N e) :=
  (Array.primrec_product Lists.primrec_product hx).comp
    ((primrec_array N e hm).comp Primrec.fst)
    (Primrec.list_cons.comp ((Primrec.const Coeff.one).pair Primrec.snd) (Primrec.const []))

omit [Primcodable X] [Finite P] in
 theorem primrec_gcost (hc : Primrec N.gcost) : Primrec (gcost (P:=P) N) := by
  have hs : Primrec (fun l : List ℕ => l.sum) :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact hs.comp (Primrec.list_map Primrec.id (hc.comp (Primrec.snd.comp Primrec.snd)).to₂)

omit [Finite P] in
 theorem primrec_xcost (hg : Primrec N.gcost) (hx : Primrec N.xcost) :
    Primrec (xcost (P:=P) N) :=
  Primrec.nat_add.comp ((primrec_gcost N hg).comp Primrec.fst) (hx.comp Primrec.snd)

variable {Param : Type*} [Primcodable Param]
variable {fg : Param → G → Part K} {fx : Param → X → Part L}

omit [Primcodable X] in
 theorem partrec_partialGroupKey (hm : Primrec₂ N.mul) (hi : Primrec N.inv)
    (hf : Partrec₂ fg) : Partrec₂ (fun p : Param => partialGroupKey N e (fg p)) := by
  have hp : Partrec (fun p : Param × Word P G =>
      Array.collectedKey Coeff.value (fg p.1) (array N e p.2)) :=
    (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp Computable.fst
      ((primrec_array N e hm).to_comp.comp Computable.snd)
  apply hp.bind
  have hq : Partrec (fun p : (Param × Word P G) × ℕ =>
      Array.collectedKey Coeff.value (fg p.1.1) (array N e (inverse N p.1.2))) :=
    (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp (Computable.fst.comp Computable.fst)
      ((primrec_array N e hm).to_comp.comp ((primrec_inverse N hi).to_comp.comp
        (Computable.snd.comp Computable.fst)))
  exact (hq.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂

 theorem partrec_partialPointKey (hm : Primrec₂ N.mul) (hx : Primrec₂ N.act)
    (hf : Partrec₂ fx) : Partrec₂ (fun p : Param => partialPointKey N e (fx p)) :=
  (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp Computable.fst
    ((primrec_pointArray N e hm hx).to_comp.comp Computable.snd)


end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
