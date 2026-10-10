import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeGCD

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

abbrev Fraction := ℕ×ℕ
def val (x : Fraction) : ℚ := (x.1:ℚ)/x.2
def repr (q : ℚ) : Fraction := (q.num.natAbs,q.den)

def normalize (x : Fraction) : Fraction :=
  if x.2=0 then (0,1) else (x.1/(x.1.gcd x.2),x.2/(x.1.gcd x.2))

def normalizeRealizer : Realizer normalize := by
  let G := gcd
  let Q := pair (composition (pair first G) quotient) (composition (pair second G) quotient)
  exact (choose (composition (pair second (constant 0)) natEqual) (constant (0,1)) Q).congr
    (fun x=>by simp only [normalize,Function.comp_apply,decide_eq_true_eq])

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma normalize_size_num (x : Fraction) : (normalize x).1.size≤x.1.size := by
  unfold normalize; split_ifs
  · simp
  · exact Nat.size_le_size (Nat.div_le_self _ _)
lemma normalize_size_den (x : Fraction) : (normalize x).2.size≤x.2.size+1 := by
  unfold normalize; split_ifs
  · simp
  · exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (Nat.le_succ _)

def mul (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.1,x.1.2*x.2.2)
def mulRealizer : Realizer mul :=
  composition (pair (composition (pair (composition first first) (composition second first)) multiply)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

def add (x : Fraction×Fraction) : Fraction :=
  normalize (x.1.1*x.2.2+x.2.1*x.1.2,x.1.2*x.2.2)
def addRealizer : Realizer add :=
  composition (pair (composition (pair
    (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.add)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

def div (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.2,x.1.2*x.2.1)
def divRealizer : Realizer div :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition first second) (composition second first)) multiply)) normalizeRealizer
lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

def less (x : Fraction×Fraction) : Bool := decide (x.1.1*x.2.2<x.2.1*x.1.2)
def lessRealizer : Realizer less :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.less
lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
