import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryGCD
import OAI.Combinatorics.KMedian.Binary.BinaryInteger

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def parts (q : ℚ) : ℤ × ℕ := (q.num,q.den)
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
 def normalized (x : ℤ × ℕ) : ℤ × ℕ :=
  if x.2=0 then (0,1) else
    (Signed.value (Signed.sign x.1) (x.1.natAbs / x.2.gcd x.1.natAbs),x.2 / x.2.gcd x.1.natAbs)
 theorem normalized_eq (x : ℤ × ℕ) : normalized x=parts (mkRat x.1 x.2) := by
  simp only [normalized,parts,Rat.num_mkRat,Rat.den_mkRat]
  split_ifs with h
  · rfl
  · rw [Signed.value_div _ _ _ (Nat.gcd_dvd_right _ _),Signed.value_parts]

 theorem inv_eq (q : ℚ) : q⁻¹=mkRat (Signed.value (Signed.sign q.num) q.den) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  calc
    q⁻¹ = ((q.num:ℚ)/q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
    _ = (q.den:ℚ)/q.num := inv_div _ _
    _ = _ := by
      have hnum := Signed.value_parts q.num
      unfold Signed.value at hnum ⊢
      split_ifs with hn
      · rw [ite_eq_left hn] at hnum
        have haZ : (q.num.natAbs:ℤ) = -q.num := by omega
        have ha : (q.num.natAbs:ℚ) = -(q.num:ℚ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℚ)) haZ
        rw [Int.cast_neg,Int.cast_natCast,ha,neg_div_neg_eq]
      · rw [ite_eq_right hn] at hnum
        have ha : (q.num.natAbs:ℚ) = (q.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
        rw [Int.cast_natCast,ha]
end Ratio

namespace PolyProgram
noncomputable def intLT : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1 < x.2)) :=
  (intSub.comp intSign).congr _ (fun _ => by simp only [Function.comp_apply,Signed.sign,sub_neg])
noncomputable def intEQ : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1=x.2)) :=
  ((intSub.comp intAbs).comp natZero).congr _ (fun _ => by simp only [Function.comp_apply,Int.natAbs_eq_zero,sub_eq_zero])

noncomputable def mkRational : PolyProgram (encodePair Signed.encode Nat.bits) Ratio.encode (fun x => mkRat x.1 x.2) := by
  let pn := fst Signed.encode Nat.bits
  let pd := snd Signed.encode Nat.bits
  let pa := pn.comp intAbs
  let pg := (pd.fanout pa).comp natGcd
  let nm := (((pn.comp intSign).fanout ((pa.fanout pg).comp natDiv)).comp intFromParts)
  let dm := (pd.fanout pg).comp natDiv
  let normal := ite (pd.comp natZero) (nm.fanout dm)
    (constant (encodePair Signed.encode Nat.bits) (encodePair Signed.encode Nat.bits) (0,1))
  refine normal.recode id (fun _ => rfl) ?_
  intro x
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
  change encodePair Signed.encode Nat.bits (Ratio.normalized x)=Ratio.encode (mkRat x.1 x.2)
  rw [Ratio.normalized_eq]
  rfl

noncomputable def ratNum : PolyProgram Ratio.encode Signed.encode Rat.num :=
  (fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratNeg : PolyProgram Ratio.encode Ratio.encode Neg.neg := by
  refine (((ratNum.comp intNeg).fanout ratDen)).recode id (fun _ => rfl) ?_
  intro q
  simp only [Function.comp_apply,id_eq,Ratio.encode,Ratio.parts,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def ratOfInt : PolyProgram Signed.encode Ratio.encode Int.cast :=
  (((identity Signed.encode).fanout (constant Signed.encode Nat.bits 1)).comp mkRational).congr _ (fun z => by simp [Rat.mkRat_eq_div])
noncomputable def ratOfNat : PolyProgram Nat.bits Ratio.encode Nat.cast :=
  (intOfNat.comp ratOfInt).congr _ (fun n => by simp)
noncomputable def ratMul : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1*x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pn := ((px.comp ratNum).fanout (py.comp ratNum)).comp intMul
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.mul_def' x.1 x.2).symm)
noncomputable def ratAdd : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1+x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pnx := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let pny := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  let pn := (pnx.fanout pny).comp intAdd
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.add_def' x.1 x.2).symm)
noncomputable def ratSub : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1-x.2) :=
  ((ratNeg.second Ratio.encode).comp ratAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
noncomputable def ratInv : PolyProgram Ratio.encode Ratio.encode Inv.inv :=
  (((((ratNum.comp intSign).fanout ratDen).comp intFromParts).fanout (ratNum.comp intAbs)).comp mkRational).congr _ (fun q => (Ratio.inv_eq q).symm)
noncomputable def ratDiv : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1/x.2) :=
  ((ratInv.second Ratio.encode).comp ratMul).congr _ (fun x => (div_eq_mul_inv x.1 x.2).symm)
noncomputable def ratLT : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1 < x.2)) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let lhs := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let rhs := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  refine ((lhs.fanout rhs).comp intLT).congr _ ?_
  intro x
  simp only [Function.comp_apply]
  simp only [← Rat.lt_iff]
end PolyProgram
end MetricKMedian.Binary
end

end OAI
