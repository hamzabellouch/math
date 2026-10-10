import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MulComputes

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
@[simp] lemma extractPrefix_pairBits (x y : List Bool) : extractPrefix (pairBits (x,y))=x := extractPrefix_pair x y
@[simp] lemma discardPrefix_pairBits (x y : List Bool) : discardPrefix (pairBits (x,y))=y := discardPrefix_pair x y
@[simp] lemma Signed.sign_encode (z : ℤ) : Signed.sign (Signed.encode z)=decide (z<0) := rfl
namespace BinaryRational

@[simp] lemma numerator_encode (x : ℚ) : numerator (encode x)=Signed.encode x.num := extractPrefix_pair _ _
@[simp] lemma denominator_encode (x : ℚ) : denominator (encode x)=x.den.bits := discardPrefix_pair _ _
@[simp] lemma decode_pair (n : ℤ) (d : ℕ) : decode (pairBits (Signed.encode n,d.bits))=mkRat n d := by
  simp only [decode,numerator,denominator,extractPrefix_pairBits,discardPrefix_pairBits,
    Signed.encode_decode,value_bits]

def leftNum (x : List Bool) : List Bool := numerator (extractPrefix x)
def rightNum (x : List Bool) : List Bool := numerator (discardPrefix x)
def leftDen (x : List Bool) : List Bool := denominator (extractPrefix x)
def rightDen (x : List Bool) : List Bool := denominator (discardPrefix x)
noncomputable def leftNum_computes : PolyComputes leftNum := extractPrefix_computes.comp numerator_computes
noncomputable def rightNum_computes : PolyComputes rightNum := discardPrefix_computes.comp numerator_computes
noncomputable def leftDen_computes : PolyComputes leftDen := extractPrefix_computes.comp denominator_computes
noncomputable def rightDen_computes : PolyComputes rightDen := discardPrefix_computes.comp denominator_computes

def rawMul (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*Signed.decode (rightNum x)),
    (value (leftDen x)*value (rightDen x)).bits)
def rawAdd (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*(value (rightDen x):ℤ)+
    Signed.decode (rightNum x)*(value (leftDen x):ℤ)),
    (value (leftDen x)*value (rightDen x)).bits)

noncomputable def rawMul_computes : PolyComputes rawMul :=
  (Signed.mul leftNum_computes rightNum_computes).pair (NatOps.mul leftDen_computes rightDen_computes)
noncomputable def rawAdd_computes : PolyComputes rawAdd := by
  have hl := Signed.mul leftNum_computes (Signed.cast_computes rightDen_computes)
  have hr := Signed.mul rightNum_computes (Signed.cast_computes leftDen_computes)
  have hn := Signed.add hl hr
  have hd := NatOps.mul leftDen_computes rightDen_computes
  have hh := hn.pair hd
  unfold rawAdd
  simpa only [Signed.encode_decode] using hh

def addWords : List Bool → List Bool := reduce ∘ rawAdd
def mulWords : List Bool → List Bool := reduce ∘ rawMul
noncomputable def addWords_computes : PolyComputes addWords := rawAdd_computes.comp reduce_computes
noncomputable def mulWords_computes : PolyComputes mulWords := rawMul_computes.comp reduce_computes

lemma addWords_pair (x y : ℚ) : addWords (pairBits (encode x,encode y))=encode (x+y) := by
  have h := Rat.mkRat_add_mkRat x.num y.num x.den_nz y.den_nz
  simp only [Rat.mkRat_self] at h
  simp only [addWords,Function.comp_apply,reduce_correct,rawAdd,leftNum,rightNum,leftDen,rightDen,
    extractPrefix_pairBits,discardPrefix_pairBits,numerator_encode,denominator_encode,
    Signed.encode_decode,value_bits,decode_pair]
  change encode (mkRat (x.num*(y.den:ℤ)+y.num*(x.den:ℤ)) (x.den*y.den))=encode (x+y)
  rw [← h]

lemma mulWords_pair (x y : ℚ) : mulWords (pairBits (encode x,encode y))=encode (x*y) := by
  simp only [mulWords,Function.comp_apply,reduce_correct,rawMul,leftNum,rightNum,leftDen,rightDen,
    extractPrefix_pairBits,discardPrefix_pairBits,numerator_encode,denominator_encode,
    Signed.encode_decode,value_bits,decode_pair]
  rw [← Rat.mul_eq_mkRat]

noncomputable def addition : Turing.TM2ComputableInPolyTime
    (fun p : ℚ×ℚ=>pairBits (encode p.1,encode p.2)) encode (fun p=>p.1+p.2) :=
  addWords_computes.reencode _ _ (fun p=>addWords_pair p.1 p.2)
noncomputable def multiplication : Turing.TM2ComputableInPolyTime
    (fun p : ℚ×ℚ=>pairBits (encode p.1,encode p.2)) encode (fun p=>p.1*p.2) :=
  mulWords_computes.reencode _ _ (fun p=>mulWords_pair p.1 p.2)

def leWords (x : List Bool) : List Bool :=
  [decide (Signed.decode (leftNum x)*(value (rightDen x):ℤ) ≤
    Signed.decode (rightNum x)*(value (leftDen x):ℤ))]
noncomputable def leWords_computes : PolyComputes leWords := by
  have hl := Signed.mul leftNum_computes (Signed.cast_computes rightDen_computes)
  have hr := Signed.mul rightNum_computes (Signed.cast_computes leftDen_computes)
  have hh := Signed.le hl hr
  unfold leWords
  simpa only [Signed.encode_decode] using hh
lemma leWords_pair (x y : ℚ) : leWords (pairBits (encode x,encode y))=[decide (x≤y)] := by
  simp only [leWords,leftNum,rightNum,leftDen,rightDen,extractPrefix_pairBits,discardPrefix_pairBits,
    numerator_encode,denominator_encode,Signed.encode_decode,value_bits,Rat.le_iff]
noncomputable def lessEqual : Turing.TM2ComputableInPolyTime
    (fun p : ℚ×ℚ=>pairBits (encode p.1,encode p.2)) (fun b:Bool=>[b]) (fun p=>decide (p.1≤p.2)) :=
  leWords_computes.reencode _ _ (fun p=>leWords_pair p.1 p.2)

def negWords (x : List Bool) : List Bool :=
  pairBits (Signed.encode (-Signed.decode (numerator x)),denominator x)
noncomputable def negWords_computes : PolyComputes negWords :=
  (Signed.neg numerator_computes).pair denominator_computes
lemma negWords_encode (x : ℚ) : negWords (encode x)=encode (-x) := by
  simp only [negWords,numerator_encode,denominator_encode,Signed.encode_decode]
  simp only [encode,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def negation : Turing.TM2ComputableInPolyTime encode encode (fun x:ℚ=>-x) :=
  negWords_computes.reencode _ _ negWords_encode

lemma signed_sign (z : ℤ) (d : ℕ) (hz : z≠0) :
    Signed.signed (decide (z<0)) d=z.sign*(d:ℤ) := by
  by_cases h : z<0
  · simp only [h,decide_true,Signed.signed,ite_true,Int.sign_eq_neg_one_of_neg h,neg_one_mul]
  · have hp : 0<z := by omega
    simp only [h,decide_false,Signed.signed,Bool.false_eq_true,ite_false,Int.sign_eq_one_of_pos hp,one_mul]

def rawInv (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x)) (value (denominator x)).bits,
    (Signed.mag (numerator x)).bits)
def invWords : List Bool → List Bool := reduce ∘ rawInv
noncomputable def rawInv_computes : PolyComputes rawInv := by
  have hs := numerator_computes.comp Signed.sign_computes
  have hd := denominator_computes.comp BinaryArithmetic.normalize_computes
  have hn := (numerator_computes.comp tail_computes).comp BinaryArithmetic.normalize_computes
  have hh := (Signed.pack_computes hs hd).pair hn
  unfold rawInv Signed.mag
  simpa only [Function.comp_def,normalize_eq_bits] using hh
noncomputable def invWords_computes : PolyComputes invWords := rawInv_computes.comp reduce_computes
lemma invWords_encode (x : ℚ) : invWords (encode x)=encode x⁻¹ := by
  simp only [invWords,Function.comp_apply,reduce_correct,rawInv,numerator_encode,denominator_encode,
    Signed.encode_mag,Signed.sign_encode,value_bits,
    Signed.pack_bits,decode_pair]
  by_cases hz : x.num=0
  · have hx : x=0 := Rat.num_eq_zero.mp hz
    subst x
    simp only [Rat.num_zero,Int.natAbs_zero,Rat.mkRat_zero,inv_zero]
  · rw [signed_sign x.num x.den hz]
    exact congrArg encode (by simpa only [Rat.num_inv,Rat.den_inv,hz,ite_false] using Rat.mkRat_self x⁻¹)
noncomputable def inverse : Turing.TM2ComputableInPolyTime encode encode (fun x:ℚ=>x⁻¹) :=
  invWords_computes.reencode _ _ invWords_encode

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
