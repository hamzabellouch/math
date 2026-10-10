import OAI.MathematicalPhysics.RapidForcing.ExprCoding

namespace OAI

section

open Encodable Denumerable Function Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Computable.option_getD
  Primrec.list_length Primrec.list_reverse Primrec.list_head? Primrec.list_tail
  Primrec.list_range

@[fun_prop] lemma primrec_list_cons {A : Type} [Primcodable A] :
    Primrec (fun p : A × List A => p.1 :: p.2) := Primrec.list_cons

lemma computable_list_casesOn {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → B × List B → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => List.casesOn (motive := fun _ => S) (f a) (g a) fun b l => h a (b, l)) := by
  have hd : Computable (fun a => (f a).head?) := Primrec.list_head?.to_comp.comp hf
  have ht : Computable (fun a => (f a).tail) := Primrec.list_tail.to_comp.comp hf
  exact (Computable.option_casesOn hd hg
    (hh.comp Computable.fst (Computable.snd.pair (ht.comp Computable.fst))).to₂).of_eq
      (fun a => by cases hfa : f a <;> simp [hfa])

lemma computable_nat_iterate {A S : Type} [Primcodable A] [Primcodable S]
    {f : A → ℕ} {g : A → S} {h : A → S → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (h a)^[f a] (g a)) := by
  exact (Computable.nat_rec hf hg
    ((hh.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂)).of_eq
    (fun a => by induction f a <;> simp [Function.iterate_succ_apply', *])

lemma computable_list_foldl {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → S × B → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s, b)) (g a)) := by
  let G (a : A) (v : S × List B) : S × List B :=
    List.casesOn v.2 v fun b l => (h a (v.1, b), l)
  have hG : Computable₂ G := computable_list_casesOn
    (Computable.snd.comp Computable.snd) Computable.snd
    ((hh.comp (Computable.fst.comp Computable.fst)
      (((Computable.fst.comp Computable.snd).comp Computable.fst).pair (Computable.fst.comp Computable.snd))).pair
      (Computable.snd.comp Computable.snd)).to₂
  have F := computable_nat_iterate (Computable.list_length.comp hf) (hg.pair hf) hG
  have he (a : A) (n : ℕ) (l : List B) (x : S) :
      (G a)^[n] (x, l) = ((l.take n).foldl (fun s b => h a (s, b)) x, l.drop n) := by
    induction n generalizing l x with
    | zero => rfl
    | succ n ih => cases l <;> simp [iterate_succ, comp_apply, G, ih]
  exact (Computable.fst.comp F).of_eq (fun a => by rw [he]; simp)

lemma computable_list_foldr {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → B × S → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b s => h a (b, s)) (g a)) := by
  exact (computable_list_foldl (Computable.list_reverse.comp hf) hg
    (hh.comp Computable.fst ((Computable.snd.pair Computable.fst).comp Computable.snd)).to₂).of_eq
      (fun a => by rw [List.foldl_reverse])

lemma computable_list_rec {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → B × List B × S → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => List.recOn (motive := fun _ => S) (f a) (g a) fun b l s => h a (b, l, s)) := by
  have hstep : Computable (fun v : A × B × List B × S =>
      (v.2.1 :: v.2.2.1, h v.1 (v.2.1, v.2.2.1, v.2.2.2))) :=
    (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
      (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair hh
  have hr := computable_list_foldr hf ((Computable.const ([] : List B)).pair hg) hstep.to₂
  apply (Computable.snd.comp hr).of_eq
  intro a
  have haux (l : List B) :
      l.foldr (fun b p => (b :: p.1, h a (b, p.1, p.2))) ([], g a) =
        (l, List.recOn (motive := fun _ => S) l (g a) fun b l s => h a (b, l, s)) := by
    induction l <;> simp [*]
  rw [haux]

end RapidForcing.EffectiveArithmetic

namespace RapidForcing.EffectiveProfile.Expr
open EffectiveArithmetic
local instance recursiveCodeDecidableEq : DecidableEq Code :=
  Encodable.decidableEqOfEncodable Code

lemma computable_recOn {A S : Type} [Primcodable A] [Primcodable S]
    {e : A → Expr} (he : Computable e)
    {c : A → ℚ → S} (hc : Computable₂ c)
    {l r : A → GluePoly → S} (hl : Computable₂ l) (hr : Computable₂ r)
    {d : A → ℕ → S} (hd : Computable₂ d)
    {a m : A → Expr × Expr × S × S → S} (ha : Computable₂ a) (hm : Computable₂ m) :
    Computable (fun x => Expr.recOn (motive := fun _ => S) (e x) (c x) (l x) (r x) (d x)
      (fun e₁ e₂ v₁ v₂ => a x (e₁, e₂, v₁, v₂))
      (fun e₁ e₂ v₁ v₂ => m x (e₁, e₂, v₁, v₂))) := by
  let z := fun x => c x 0
  let pr := fun (x : A) (p : Code × Code × S × S) =>
    if p.1 = .zero then c x ((decode (encode p.2.1)).getD 0)
    else if p.1 = .succ then l x ((decode (encode p.2.1)).getD [])
    else if p.1 = .left then r x ((decode (encode p.2.1)).getD [])
    else d x (encode p.2.1)
  let co := fun (x : A) (p : Code × Code × S × S) =>
    a x (fromCode p.1, fromCode p.2.1, p.2.2.1, p.2.2.2)
  let pc := fun (x : A) (p : Code × Code × S × S) =>
    m x (fromCode p.1, fromCode p.2.1, p.2.2.1, p.2.2.2)
  have hz : Computable z := hc.comp Computable.id (Computable.const 0)
  have hpr : Computable₂ pr := by
    unfold pr Computable₂
    apply computable_ite (by fun_prop) (hc.comp Computable.fst (by fun_prop))
    apply computable_ite (by fun_prop) (hl.comp Computable.fst (by fun_prop))
    exact computable_ite (by fun_prop) (hr.comp Computable.fst (by fun_prop))
      (hd.comp Computable.fst (by fun_prop))
  have hco : Computable₂ co := ha.comp Computable.fst (by fun_prop)
  have hpc : Computable₂ pc := hm.comp Computable.fst (by fun_prop)
  have H := Code.computable_recOn (primrec_toCode.to_comp.comp he) hz hz hz hz
    hpr hco hpc (rf := fun x _ => z x) (hz.comp Computable.fst).to₂
  apply H.of_eq
  intro x
  have hh (b : Code) : Code.recOn b (z x) (z x) (z x) (z x)
      (fun c₁ c₂ v₁ v₂ => pr x (c₁, c₂, v₁, v₂))
      (fun c₁ c₂ v₁ v₂ => co x (c₁, c₂, v₁, v₂))
      (fun c₁ c₂ v₁ v₂ => pc x (c₁, c₂, v₁, v₂)) (fun _ _ => z x) =
      Expr.recOn (motive := fun _ => S) (fromCode b) (c x) (l x) (r x) (d x)
        (fun e₁ e₂ v₁ v₂ => a x (e₁, e₂, v₁, v₂))
        (fun e₁ e₂ v₁ v₂ => m x (e₁, e₂, v₁, v₂)) := by
    induction b <;> simp_all only [fromCode, pr, co, pc, z]
    split_ifs <;> rfl
  simpa only [fromCode_toCode] using hh (toCode (e x))

end RapidForcing.EffectiveProfile.Expr

end

end OAI
