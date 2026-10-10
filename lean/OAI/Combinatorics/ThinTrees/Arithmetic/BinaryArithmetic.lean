import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialExplicit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialRoots
import OAI.Analysis.MatrixSigning.Realization.OriginalOutputRoutine
import OAI.Combinatorics.ThinTrees.BasePacking

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

def wordCons (b : Bool) : Realizes wordCode wordCode (fun w => b::w) where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W07.SchurCounters.pushProgram 0 b
    spec := fun w => by
      have h := KS.W07.SchurCounters.push_spec (0 : Fin 1) b (io w)
      convert h using 1 <;> (try rfl)
      funext j; fin_cases j; rfl }
instance poly_wordCons (b : Bool) : PolyTime (wordCons b) := ⟨⟨1,fun _ => le_rfl⟩⟩

def binaryToRat : Realizes binaryNatCode ratCode (fun n => (n:ℚ)) :=
  ((((identity binaryNatCode).both (constant binaryNatCode KS.W01.encodeNat 1)).changeOutput
    wordCode (fun n => prodCode binaryNatCode KS.W01.encodeNat (n,1)) (fun _ => rfl)).then
    (wordCons false)).changeOutput ratCode (fun n => (n:ℚ)) (fun n => by
      simp only [ratCode,KS.W01.encodeRat,Rat.num_natCast,Rat.den_natCast,
        KS.W01.encodeInt,prodCode,PairRoutine.pair,binaryNatCode,KS.W01.encodeNat]
      rfl)
instance poly_binaryToRat : PolyTime binaryToRat := by unfold binaryToRat;infer_instance

lemma intPayload_natCast (n : ℕ) : KS.W01.intPayload (n:ℤ)=n := rfl

def binaryDiv (d : ℕ) : Realizes binaryNatCode binaryNatCode (fun n => n/d) :=
  (((binaryToRat.div (constant binaryNatCode ratCode d)).then ratFloor).then ratNumBinary).congr
    (fun n => by
      simp only [Rat.num_intCast,Int.floor_div_natCast,Int.floor_natCast,
        ← Int.natCast_ediv,intPayload_natCast])
instance poly_binaryDiv (d : ℕ) : PolyTime (binaryDiv d) := by unfold binaryDiv;infer_instance

def binaryMod (d : ℕ) : Realizes binaryNatCode binaryNatCode (fun n => n%d) :=
  ((binaryToRat.sub ((constant binaryNatCode ratCode d).mul
    ((binaryDiv d).then binaryToRat))).then ratNumBinary).congr (fun n => by
      have he : (n:ℚ)-(d:ℚ)*(n/d:ℕ)=(n%d:ℕ) := by
        have h := Nat.mod_add_div n d
        have hh := congrArg (fun a : ℕ => (a:ℚ)) h
        push_cast at hh
        linarith
      rw [he,Rat.num_natCast,intPayload_natCast])
instance poly_binaryMod (d : ℕ) : PolyTime (binaryMod d) := by unfold binaryMod;infer_instance

def binaryModUnary (d : ℕ) : Realizes binaryNatCode natCode (fun n => n%d) :=
  (binaryMod d).then binaryToNat
instance poly_binaryModUnary (d : ℕ) [hd : Fact (0<d)] : PolyTime (binaryModUnary d) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=binaryMod d)
  refine ⟨⟨5*p+4*X+NaturalPolynomial.constant (6*d+4),?_⟩⟩
  intro n
  have ho := (binaryMod d).output_length n
  have hn := Nat.mod_lt n hd.out
  have hh := hp n
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤_
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤
    5*p.eval (binaryNatCode n).length+4*(binaryNatCode n).length+(6*d+4)
  omega

def ratDenRat : Realizes ratCode ratCode (fun q => (q.den:ℚ)) := ratDenBinary.then binaryToRat
instance poly_ratDenRat : PolyTime ratDenRat := by unfold ratDenRat;infer_instance

def scalarProductBinary : Realizes ratCode binaryNatCode (fun q => q.num.natAbs*q.den) :=
  ((((identity ratCode).abs.mul (ratDenRat.pow 2))).then ratNumBinary).congr (fun q => by
    have he : |q| *(q.den:ℚ)^2=(q.num.natAbs*q.den:ℕ) := by
      rw [show |q|=|(q.num:ℚ)/(q.den:ℚ)| from congrArg abs (Rat.num_div_den q).symm,
        abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)]
      push_cast
      rw [Nat.cast_natAbs,Int.cast_abs]
      field_simp
    change KS.W01.intPayload (|q| * (q.den:ℚ)^2).num=_
    rw [he,Rat.num_natCast,intPayload_natCast])
instance poly_scalarProductBinary : PolyTime scalarProductBinary := by
  unfold scalarProductBinary;infer_instance

end CurrentKS.Realization
end

end OAI
