import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinarySubtraction
import OAI.Combinatorics.KMedian.Binary.BinaryMultiplication

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def value (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else n
 def sign (z : ℤ) : Bool := decide (z < 0)
 def parts (z : ℤ) : Bool × ℕ := (sign z,z.natAbs)
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

 theorem abs_value (s : Bool) (n : ℕ) : (value s n).natAbs=n := by cases s <;> simp [value]
 theorem sign_value (s : Bool) (n : ℕ) : sign (value s n)=(s && !decide (n=0)) := by
  cases s <;> by_cases hn : n=0
  all_goals simp only [value,sign,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp [hn, Nat.pos_of_ne_zero]

 theorem value_parts (z : ℤ) : value (sign z) z.natAbs=z := by
  unfold value sign
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt (of_decide_eq_true h))).symm
  · exact Int.natAbs_of_nonneg (by simpa using h)

 theorem value_neg (s : Bool) (n : ℕ) : value (!s) n= -value s n := by
  cases s <;> simp [value]

 theorem value_mul (s t : Bool) (n m : ℕ) : value (xor s t) (n*m)=value s n*value t m := by
  cases s <;> cases t <;> simp [value]

 def add (s t : Bool) (n m : ℕ) : ℤ :=
  if s=t then value s (n+m) else if n < m then value t (m-n) else value s (n-m)

 theorem value_add (s t : Bool) (n m : ℕ) : add s t n m=value s n+value t m := by
  cases s <;> cases t <;> by_cases h : n < m <;> simp [add,value,h] <;> omega

 theorem value_div (s : Bool) (n d : ℕ) (h : d∣n) : value s (n/d)=value s n/(d:ℤ) := by
  have hd : (d:ℤ)∣(n:ℤ) := Int.natCast_dvd_natCast.mpr h
  cases s <;> simp only [value,Bool.false_eq_true,ite_false,ite_true,Int.neg_ediv_of_dvd hd,Int.ofNat_ediv_ofNat]
end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intFromParts : PolyProgram signedParts Signed.encode (fun x => Signed.value x.1 x.2) := by
  let ps := fst encodeBool Nat.bits
  let pn := snd encodeBool Nat.bits
  let s := (ps.fanout ((pn.comp natZero).comp boolNot)).comp boolAnd
  exact (s.fanout pn).recode id (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,id_eq,Signed.encode,Signed.parts,Signed.sign_value,Signed.abs_value])

noncomputable def intSign : PolyProgram Signed.encode encodeBool Signed.sign :=
  (fst encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def intAbs : PolyProgram Signed.encode Nat.bits Int.natAbs :=
  (snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)

noncomputable def intNeg : PolyProgram Signed.encode Signed.encode Neg.neg :=
  (((intSign.comp boolNot).fanout intAbs).comp intFromParts).congr _ (fun z => by
    simp only [Function.comp_apply,Signed.value_neg,Signed.value_parts])

noncomputable def intOfNat : PolyProgram Nat.bits Signed.encode Nat.cast :=
  (((constant Nat.bits encodeBool false).fanout (identity Nat.bits)).comp intFromParts).congr _ (fun _ => rfl)

noncomputable def boolXor : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => xor x.1 x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolEq : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => decide (x.1=x.2)) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

noncomputable def intMul : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1*x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let s := ((px.comp intSign).fanout (py.comp intSign)).comp boolXor
  let n := ((px.comp intAbs).fanout (py.comp intAbs)).comp natMul
  exact ((s.fanout n).comp intFromParts).congr _ (fun x => by
    simp only [Function.comp_apply,Signed.value_mul,Signed.value_parts])

noncomputable def intAdd : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1+x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let sx := px.comp intSign
  let sy := py.comp intSign
  let nx := px.comp intAbs
  let ny := py.comp intAbs
  let plus := ((sx.fanout ((nx.fanout ny).comp natAdd)).comp intFromParts)
  let minusX := (sx.fanout ((nx.fanout ny).comp natSub)).comp intFromParts
  let minusY := (sy.fanout ((ny.fanout nx).comp natSub)).comp intFromParts
  let minus := ite ((nx.fanout ny).comp natLT) minusX minusY
  refine (ite ((sx.fanout sy).comp boolEq) minus plus).congr _ ?_
  intro x
  simpa only [Function.comp_apply, decide_eq_true_eq, Signed.add, Signed.value_parts]
    using Signed.value_add (Signed.sign x.1) (Signed.sign x.2) x.1.natAbs x.2.natAbs

noncomputable def intSub : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1-x.2) :=
  ((intNeg.second Signed.encode).comp intAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
