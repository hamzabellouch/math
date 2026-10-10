import OAI.MathematicalPhysics.RapidForcing.RationalProfiles
import OAI.MathematicalPhysics.RapidForcing.ComputableAutomation
import OAI.MathematicalPhysics.RapidForcing.RatPrimrec

namespace OAI


open Encodable Denumerable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma primrec_code_pair : Primrec (fun p : Code × Code => Code.pair p.1 p.2) :=
  Code.primrec₂_pair
@[fun_prop] lemma primrec_code_comp : Primrec (fun p : Code × Code => Code.comp p.1 p.2) :=
  Code.primrec₂_comp
@[fun_prop] lemma primrec_code_prec : Primrec (fun p : Code × Code => Code.prec p.1 p.2) :=
  Code.primrec₂_prec
attribute [fun_prop] Nat.Partrec.Code.primrec_rfind'
@[fun_prop] lemma primrec_code_ofNat : Primrec Code.ofNatCode := Primrec.ofNat Code

@[instance_reducible] def retractEncodable {A B : Type} [Encodable B] (f : A → B) (g : B → A)
    (h : Function.LeftInverse g f) : Encodable A := Encodable.ofLeftInverse f g h

@[instance_reducible] def primcodable_retract {A B : Type} [Primcodable B] (f : A → B) (g : B → A)
    (h : Function.LeftInverse g f) (hr : Primrec (fun b => f (g b))) :
    Primcodable A :=
  { toEncodable := retractEncodable f g h
    prim := by
      let := retractEncodable f g h
      have hp := Primrec.nat_iff.mp <| Primrec.encode.comp <|
        Primrec.option_map Primrec.decode (hr.comp Primrec.snd).to₂
      apply hp.of_eq
      intro n
      change encode ((decode (α := B) n).map (fun b => f (g b))) =
        @encode (Option A) _ ((decode (α := B) n).bind (some ∘ g))
      cases decode (α := B) n <;> rfl }

@[simp] lemma code_encode_ofNat (n : ℕ) : encode (Code.ofNatCode n) = n :=
  Denumerable.encode_ofNat (α := Code) n

end RapidForcing.EffectiveArithmetic

namespace RapidForcing.EffectiveProfile
open EffectiveArithmetic
namespace Expr

local instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code

def toCode : Expr → Code
  | .const q => .pair .zero (.ofNatCode (encode q))
  | .left p => .pair .succ (.ofNatCode (encode p))
  | .right p => .pair .left (.ofNatCode (encode p))
  | .invDen n => .pair .right (.ofNatCode n)
  | .add a b => .comp a.toCode b.toCode
  | .mul a b => .prec a.toCode b.toCode

def fromCode : Code → Expr
  | .pair t v => if t = .zero then .const ((decode (encode v)).getD 0)
      else if t = .succ then .left ((decode (encode v)).getD [])
      else if t = .left then .right ((decode (encode v)).getD [])
      else .invDen (encode v)
  | .comp a b => .add (fromCode a) (fromCode b)
  | .prec a b => .mul (fromCode a) (fromCode b)
  | _ => .const 0

@[simp] lemma fromCode_toCode (e : Expr) : fromCode e.toCode = e := by
  induction e <;> simp [toCode, fromCode, *]

lemma primrec_normalize : Primrec (fun c => toCode (fromCode c)) := by
  let z : Code := toCode (.const 0)
  have h := Code.primrec_recOn (σ := Code) Primrec.id
    (Primrec.const z) (Primrec.const z) (Primrec.const z) (Primrec.const z)
    (pr := fun _ t v _ _ => if t = .zero then toCode (.const ((decode (encode v)).getD 0))
      else if t = .succ then toCode (.left ((decode (encode v)).getD []))
      else if t = .left then toCode (.right ((decode (encode v)).getD []))
      else toCode (.invDen (encode v)))
    (by
      dsimp [toCode]
      apply Primrec.ite (by fun_prop) _ _
      · apply primrec_code_pair.comp ((Primrec.const _).pair ?_)
        exact primrec_code_ofNat.comp <| Primrec.encode.comp <|
          Primrec.option_getD.comp (Primrec.decode.comp (Primrec.encode.comp (by fun_prop))) (Primrec.const 0)
      · apply Primrec.ite (by fun_prop) _ _
        · apply primrec_code_pair.comp ((Primrec.const _).pair ?_)
          exact primrec_code_ofNat.comp <| Primrec.encode.comp <|
            Primrec.option_getD.comp (Primrec.decode.comp (Primrec.encode.comp (by fun_prop))) (Primrec.const [])
        · apply Primrec.ite (by fun_prop) _ _
          · apply primrec_code_pair.comp ((Primrec.const _).pair ?_)
            exact primrec_code_ofNat.comp <| Primrec.encode.comp <|
              Primrec.option_getD.comp (Primrec.decode.comp (Primrec.encode.comp (by fun_prop))) (Primrec.const [])
          · fun_prop)
    (co := fun _ _ _ a b => .comp a b) (by fun_prop)
    (pc := fun _ _ _ a b => .prec a b) (by fun_prop)
    (rf := fun _ _ _ => z) (by fun_prop)
  apply h.of_eq
  intro c
  induction c <;> simp_all only [id_eq, fromCode, toCode]
  all_goals first | rfl | (split_ifs <;> rfl)

instance : Primcodable Expr := primcodable_retract toCode fromCode fromCode_toCode primrec_normalize

@[fun_prop] lemma primrec_toCode : Primrec toCode := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec (@encode Expr _))

@[fun_prop] lemma primrec_fromCode : Primrec fromCode := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.comp primrec_normalize

@[simp] lemma encode_toCode (e : Expr) : encode (toCode e) = encode e := rfl

@[fun_prop] lemma primrec_const : Primrec Expr.const := by
  apply Primrec.encode_iff.mp
  change Primrec (fun q => encode (toCode (.const q)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_left : Primrec Expr.left := by
  apply Primrec.encode_iff.mp
  change Primrec (fun q => encode (toCode (.left q)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_right : Primrec Expr.right := by
  apply Primrec.encode_iff.mp
  change Primrec (fun q => encode (toCode (.right q)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_invDen : Primrec Expr.invDen := by
  apply Primrec.encode_iff.mp
  change Primrec (fun q => encode (toCode (.invDen q)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_add : Primrec (fun p : Expr × Expr => Expr.add p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Expr × Expr => encode (toCode (.add p.1 p.2)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_mul : Primrec (fun p : Expr × Expr => Expr.mul p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Expr × Expr => encode (toCode (.mul p.1 p.2)))
  unfold toCode
  fun_prop

end Expr
end RapidForcing.EffectiveProfile

end OAI
