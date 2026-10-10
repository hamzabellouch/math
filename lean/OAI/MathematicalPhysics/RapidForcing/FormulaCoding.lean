import OAI.MathematicalPhysics.RapidForcing.FieldExpressions
import OAI.MathematicalPhysics.RapidForcing.RecursiveComputable

namespace OAI

section
open Encodable Denumerable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic
local instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code

def codeUnary (c : Code) : Code := match c with | .rfind' a => a | _ => .zero
@[simp] lemma codeUnary_rfind (a : Code) : codeUnary (.rfind' a) = a := rfl
@[fun_prop] lemma primrec_codeUnary : Primrec codeUnary := by
  have h := Code.primrec_recOn Primrec.id
    (Primrec.const Code.zero) (Primrec.const Code.zero)
    (Primrec.const Code.zero) (Primrec.const Code.zero)
    (pr := fun _ _ _ _ _ => Code.zero) (by fun_prop)
    (co := fun _ _ _ _ _ => Code.zero) (by fun_prop)
    (pc := fun _ _ _ _ _ => Code.zero) (by fun_prop)
    (rf := fun _ a _ => a) (by fun_prop)
  exact h.of_eq (fun c => by cases c <;> rfl)
end RapidForcing.EffectiveArithmetic

namespace RapidForcing.EffectiveProfile.Formula
open EffectiveArithmetic
local instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code
variable {d : ℕ}

def toCode : Formula d → Code
  | .const q => .pair .zero (.ofNatCode (encode q))
  | .var i => .pair .succ (.ofNatCode (encode i))
  | .add a b => .comp a.toCode b.toCode
  | .mul a b => .prec a.toCode b.toCode
  | .profile e a => .pair (.rfind' e.toCode) a.toCode

def fromCode : Code → Formula d
  | .pair t v => if t = .zero then .const ((decode (encode v)).getD 0)
      else if t = .succ then ((decode (encode v)).map Formula.var).getD (.const 0)
      else .profile (Expr.fromCode (codeUnary t)) (fromCode v)
  | .comp a b => .add (fromCode a) (fromCode b)
  | .prec a b => .mul (fromCode a) (fromCode b)
  | _ => .const 0

@[simp] lemma fromCode_toCode (a : Formula d) : fromCode a.toCode = a := by
  induction a <;> simp [toCode, fromCode, *]

lemma primrec_normalize : Primrec (fun c => toCode (fromCode (d := d) c)) := by
  let z : Code := .pair .zero (.ofNatCode (encode (0 : ℚ)))
  have H := Code.primrec_recOn (σ := Code) Primrec.id
    (Primrec.const z) (Primrec.const z) (Primrec.const z) (Primrec.const z)
    (pr := fun _ t v _ w => if t = .zero then .pair .zero (.ofNatCode (encode ((decode (α := ℚ) (encode v)).getD 0)))
      else if t = .succ then ((decode (α := Fin d) (encode v)).map
        (fun i => Code.pair .succ (.ofNatCode (encode i)))).getD z
      else .pair (.rfind' (Expr.toCode (Expr.fromCode (codeUnary t)))) w)
    (by
      apply Primrec.ite (by fun_prop) _ _
      · exact primrec_code_pair.comp ((Primrec.const _).pair (primrec_code_ofNat.comp
          (Primrec.encode.comp (Primrec.option_getD.comp
            (Primrec.decode.comp (Primrec.encode.comp (by fun_prop))) (Primrec.const 0)))))
      · apply Primrec.ite (by fun_prop) _ _
        · apply Primrec.option_getD.comp _ (Primrec.const z)
          apply Primrec.option_map (Primrec.decode.comp (Primrec.encode.comp (by fun_prop)))
          unfold Primrec₂
          fun_prop
        · fun_prop)
    (co := fun _ _ _ a b => .comp a b) (by fun_prop)
    (pc := fun _ _ _ a b => .prec a b) (by fun_prop)
    (rf := fun _ _ _ => z) (by fun_prop)
  apply H.of_eq
  intro c
  induction c <;> simp_all only [id_eq, fromCode, toCode]
  all_goals first | rfl | skip
  rename_i t v ih₁ ih₂
  split_ifs with ht hs
  · rfl
  · cases decode (α := Fin d) (encode v) <;> rfl
  · simp only [toCode]

instance : Primcodable (Formula d) :=
  primcodable_retract toCode fromCode fromCode_toCode primrec_normalize

@[simp] lemma encode_toCode (a : Formula d) : encode a.toCode = encode a := rfl

@[fun_prop] lemma primrec_toCode : Primrec (@toCode d) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec (@encode (Formula d) _))

@[fun_prop] lemma primrec_fromCode : Primrec (@fromCode d) := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.comp primrec_normalize

@[fun_prop] lemma primrec_const : Primrec (@Formula.const d) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun q => encode (toCode (d := d) (.const q)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_var : Primrec (@Formula.var d) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun i : Fin d => encode (toCode (.var i)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_add : Primrec (fun p : Formula d × Formula d => Formula.add p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Formula d × Formula d => encode (toCode (.add p.1 p.2)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_mul : Primrec (fun p : Formula d × Formula d => Formula.mul p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Formula d × Formula d => encode (toCode (.mul p.1 p.2)))
  unfold toCode
  fun_prop
@[fun_prop] lemma primrec_profile : Primrec (fun p : Expr × Formula d => Formula.profile p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Expr × Formula d => encode (toCode (.profile p.1 p.2)))
  unfold toCode
  fun_prop

lemma computable_recOn {A S : Type} [Primcodable A] [Primcodable S]
    {e : A → Formula d} (he : Computable e)
    {c : A → ℚ → S} (hc : Computable₂ c)
    {v : A → Fin d → S} (hv : Computable₂ v)
    {a m : A → Formula d × Formula d × S × S → S} (ha : Computable₂ a) (hm : Computable₂ m)
    {p : A → Expr × Formula d × S → S} (hp : Computable₂ p) :
    Computable (fun x => Formula.recOn (motive := fun _ => S) (e x) (c x) (v x)
      (fun e₁ e₂ v₁ v₂ => a x (e₁, e₂, v₁, v₂))
      (fun e₁ e₂ v₁ v₂ => m x (e₁, e₂, v₁, v₂))
      (fun u e h => p x (u, e, h))) := by
  let z := fun x => c x 0
  let pr := fun (x : A) (q : Code × Code × S × S) =>
    if q.1 = .zero then c x ((decode (encode q.2.1)).getD 0)
    else if q.1 = .succ then ((decode (α := Fin d) (encode q.2.1)).map (v x)).getD (z x)
    else p x (Expr.fromCode (codeUnary q.1), fromCode q.2.1, q.2.2.2)
  let co := fun (x : A) (q : Code × Code × S × S) =>
    a x (fromCode q.1, fromCode q.2.1, q.2.2.1, q.2.2.2)
  let pc := fun (x : A) (q : Code × Code × S × S) =>
    m x (fromCode q.1, fromCode q.2.1, q.2.2.1, q.2.2.2)
  have hz : Computable z := hc.comp Computable.id (Computable.const 0)
  have hpr : Computable₂ pr := by
    unfold pr Computable₂
    apply computable_ite (by fun_prop) (hc.comp Computable.fst (by fun_prop))
    apply computable_ite (by fun_prop) _ (hp.comp Computable.fst (by fun_prop))
    apply Computable.option_getD _ (hz.comp Computable.fst)
    apply Computable.option_map (by fun_prop)
    exact (hv.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
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
      Formula.recOn (motive := fun _ => S) (fromCode (d := d) b) (c x) (v x)
        (fun e₁ e₂ v₁ v₂ => a x (e₁, e₂, v₁, v₂))
        (fun e₁ e₂ v₁ v₂ => m x (e₁, e₂, v₁, v₂))
        (fun u e h => p x (u, e, h)) := by
    induction b <;> simp_all only [fromCode, pr, co, pc, z]
    rename_i t u ih₁ ih₂
    split_ifs with ht hs
    · rfl
    · cases decode (α := Fin d) (encode u) <;> rfl
    · rfl
  simpa only [fromCode_toCode] using hh (toCode (e x))

end RapidForcing.EffectiveProfile.Formula

end

end OAI
