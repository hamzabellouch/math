import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCoordinates
import OAI.Combinatorics.ThinTrees.Arithmetic.BinaryArithmetic

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

lemma pred_iterate (n k : ℕ) : Nat.pred^[k] n = n-k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,Nat.pred_eq_sub_one]; omega

instance size_natPred : IterateSize natPred := by
  refine ⟨⟨X,?_⟩⟩
  intro n k
  change (natCode (Nat.pred^[k] n)).length ≤ (natCode n).length+k
  simp only [natCode,List.length_replicate,pred_iterate]
  omega

def natSub : Realizes (prodCode natCode natCode) natCode (fun p => p.1-p.2) :=
  (((second natCode natCode).both (first natCode natCode)).then natPred.iterate).congr
    (fun p => pred_iterate p.1 p.2)
instance poly_natSub : PolyTime natSub := by unfold natSub;infer_instance

def natDivBinary : Realizes (prodCode natCode natCode) binaryNatCode (fun p => p.1/p.2) :=
  (((((first natCode natCode).then natToRat).div
    ((second natCode natCode).then natToRat)).then ratFloor).then ratNumBinary).congr
      (fun p => by
        simp only [Rat.num_intCast,Int.floor_div_natCast,Int.floor_natCast,
          ←Int.natCast_ediv,intPayload_natCast])
instance poly_natDivBinary : PolyTime natDivBinary := by unfold natDivBinary;infer_instance

def natDiv : Realizes (prodCode natCode natCode) natCode (fun p => p.1/p.2) :=
  natDivBinary.then binaryToNat
instance poly_natDiv : PolyTime natDiv := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=natDivBinary)
  refine ⟨⟨5*p+10*X+4,?_⟩⟩
  intro a
  have hc := hp a
  have ho := natDivBinary.output_length a
  have hn := Nat.div_le_self a.1 a.2
  have hl := le_prodCode_left (ea:=natCode) (eb:=natCode) a
  simp only [natCode,List.length_replicate] at hl
  change natDivBinary.cost a+(6*(a.1/a.2)+4*(binaryNatCode (a.1/a.2)).length+4)≤
    5*p.eval (prodCode natCode natCode a).length+10*(prodCode natCode natCode a).length+4
  omega

def natMod : Realizes (prodCode natCode natCode) natCode (fun p => p.1%p.2) :=
  ((first natCode natCode).both
    (((second natCode natCode).both natDiv).then natMul)).then natSub |>.congr
      (fun p => by
        dsimp only
        have h := Nat.mod_add_div p.1 p.2
        omega)
instance poly_natMod : PolyTime natMod := by unfold natMod;infer_instance

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
def Realizes.nadd (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natAdd
def Realizes.nmul (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natMul
def Realizes.nsub (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natSub
def Realizes.ndiv (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natDiv
def Realizes.nmod (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natMod
def Realizes.neq (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natEq
def Realizes.nlt (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natLT
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nadd s) := by unfold Realizes.nadd;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmul s) := by unfold Realizes.nmul;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nsub s) := by unfold Realizes.nsub;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.ndiv s) := by unfold Realizes.ndiv;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmod s) := by unfold Realizes.nmod;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.neq s) := by unfold Realizes.neq;infer_instance
instance {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nlt s) := by unfold Realizes.nlt;infer_instance

end CurrentKS.Realization
end

end OAI
