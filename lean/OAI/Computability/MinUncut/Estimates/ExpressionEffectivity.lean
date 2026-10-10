import Mathlib
import OAI.Computability.MinUncut.Search.ArithmeticExpression

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec
lemma p_dropCode : Primrec dropCode := by
  have hh := Primrec.nat_rec₁ Code.id
    (primrec_comp.comp (Primrec.const Code.tail) Primrec.snd).to₂
  exact hh.of_eq (by intro n; induction n <;> simp_all only [Nat.rec_zero,dropCode])
lemma p_constCode : Primrec constCode := by
  have hh := Primrec.nat_rec₁ Code.zero
    (primrec_comp.comp (Primrec.const Code.succ) Primrec.snd).to₂
  exact hh.of_eq (by intro n; induction n <;> simp_all only [Nat.rec_zero,constCode])
lemma p_atCode : Primrec atCode := primrec_comp.comp (Primrec.const Code.head) p_dropCode

def bin (op a b : Code) : Code := .comp op (.cons a (.cons b .nil))
def branch (e a b : Code) : Code := .comp (.case a (.comp b .tail)) (.cons e .id)
lemma p_bin (op : Code) : Primrec₂ (bin op) :=
  primrec_comp.comp (Primrec.const op) (primrec_cons.comp Primrec.fst (primrec_cons.comp Primrec.snd (Primrec.const Code.nil)))
lemma p_branch : Primrec (fun p : Code × Code × Code=>branch p.1 p.2.1 p.2.2) :=
  primrec_comp.comp (primrec_case.comp (Primrec.fst.comp Primrec.snd)
    (primrec_comp.comp (Primrec.snd.comp Primrec.snd) (Primrec.const Code.tail)))
    (primrec_cons.comp Primrec.fst (Primrec.const Code.id))

def C {P : Type} [Primcodable P] (f : P → AExpr) : Prop :=
  Computable (fun p=>(f p).program.code)
variable {P : Type} [Primcodable P]
lemma C.fixed (a : AExpr) : C (fun _ : P=>a) := Computable.const _
lemma C.const {f : P → ℕ} (hf : Computable f) : C (fun p=>.const (f p)) := p_constCode.to_comp.comp hf
lemma C.reg {f : P → ℕ} (hf : Computable f) : C (fun p=>.reg (f p)) := p_atCode.to_comp.comp hf
lemma C.add {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.add (a p) (b p)) :=
  (p_bin PolyProgram.add.code).to_comp.comp ha hb
lemma C.sub {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.sub (a p) (b p)) :=
  (p_bin PolyProgram.sub.code).to_comp.comp ha hb
lemma C.mul {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.mul (a p) (b p)) :=
  (p_bin PolyProgram.mul.code).to_comp.comp ha hb
lemma C.div {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.div (a p) (b p)) :=
  (p_bin Division.quotient.code).to_comp.comp ha hb
lemma C.mod {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.mod (a p) (b p)) :=
  (p_bin Division.remainder.code).to_comp.comp ha hb
lemma cond_code (e a b : AExpr) :
    (.cond e a b : AExpr).program.code = branch e.program.code a.program.code b.program.code := rfl
lemma C.cond {e a b : P → AExpr} (he : C e) (ha : C a) (hb : C b) : C (fun p=>.cond (e p) (a p) (b p)) := by
  have hh := p_branch.to_comp.comp (he.pair (ha.pair hb))
  exact hh.of_eq (fun p=>(cond_code (e p) (a p) (b p)).symm)
attribute [local irreducible] PolyProgram.add PolyProgram.sub PolyProgram.mul
lemma eqOf_code {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    (PolyProgram.eqOf F G).code =
      branch (bin PolyProgram.add.code (bin PolyProgram.sub.code F.code G.code)
        (bin PolyProgram.sub.code G.code F.code)) (constCode 1) (constCode 0) := rfl
lemma eq_code (a b : AExpr) :
    (.eq a b : AExpr).program.code =
      branch (bin PolyProgram.add.code (bin PolyProgram.sub.code a.program.code b.program.code)
        (bin PolyProgram.sub.code b.program.code a.program.code)) (constCode 1) (constCode 0) :=
  eqOf_code a.program b.program
lemma le_code (a b : AExpr) :
    (.le a b : AExpr).program.code =
      branch (bin PolyProgram.sub.code a.program.code b.program.code) (constCode 1) (constCode 0) := rfl
lemma at_code (a : AExpr) : (.at a : AExpr).program.code =
    Code.comp PolyProgram.dynamic.code (Code.cons a.program.code Code.id) := rfl
lemma C.eq {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.eq (a p) (b p)) := by
  have hh := p_branch.to_comp.comp
    (((p_bin PolyProgram.add.code).to_comp.comp
      ((p_bin PolyProgram.sub.code).to_comp.comp ha hb)
      ((p_bin PolyProgram.sub.code).to_comp.comp hb ha)).pair
      ((Computable.const (constCode 1)).pair (Computable.const (constCode 0))))
  exact hh.of_eq (fun p=>(eq_code (a p) (b p)).symm)
lemma C.le {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.le (a p) (b p)) := by
  have hh := p_branch.to_comp.comp
    (((p_bin PolyProgram.sub.code).to_comp.comp ha hb).pair
      ((Computable.const (constCode 1)).pair (Computable.const (constCode 0))))
  exact hh.of_eq (fun p=>(le_code (a p) (b p)).symm)
lemma C.at {a : P → AExpr} (ha : C a) : C (fun p=>.at (a p)) := by
  have hh := computable_comp.comp (Computable.const PolyProgram.dynamic.code)
    (computable_cons.comp ha (Computable.const Code.id))
  exact hh.of_eq (fun p=>(at_code (a p)).symm)
lemma powCode_eq (a : AExpr) (n : ℕ) :
    Nat.rec (AExpr.const 1).program.code (fun _ ih=>bin PolyProgram.mul.code ih a.program.code) n =
      (a.pow n).program.code := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bin _ (Nat.rec _ _ n) _ = _
    rw [ih]; rfl
lemma C.pow {a : P → AExpr} {n : P → ℕ} (ha : C a) (hn : Computable n) : C (fun p=>(a p).pow (n p)) := by
  have hh := Computable.nat_rec (σ:=Code) hn (Computable.const (AExpr.const 1).program.code)
    ((p_bin PolyProgram.mul.code).to_comp.comp (Computable.snd.comp Computable.snd)
      (ha.comp Computable.fst)).to₂
  exact hh.of_eq (fun p=>powCode_eq (a p) (n p))

def sumCode (cs : List Code) : Code := cs.foldr (bin PolyProgram.add.code) (AExpr.const 0).program.code
lemma p_sumCode : Primrec sumCode :=
  Primrec.list_foldr Primrec.id (Primrec.const _) ((p_bin _).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
lemma sumCode_eq (as : List AExpr) : sumCode (as.map (fun a=>a.program.code))=(AExpr.sum as).program.code := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [sumCode,List.map_cons,List.foldr_cons] at *; rw [ih]; rfl
lemma C.sum {as : P → List AExpr} (h : Computable (fun p=>(as p).map (fun a=>a.program.code))) : C (fun p=>AExpr.sum (as p)) :=
  (p_sumCode.to_comp.comp h).of_eq (fun p=>sumCode_eq (as p))
end MinUncut.Preprocess.Syntax

end
end

end OAI
