import Mathlib
import OAI.GroupTheory.PeriodicGroups.Formulas.LocalPredicates

namespace OAI

universe u v w
namespace SourceBurnside.PredicateFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]
lemma rawBinaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q W X Y Z : Formula ι} (w x y z : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    (hW : W.eval v=natCode w) (hX : X.eval v=natCode x) (hY : Y.eval v=natCode y) (hZ : Z.eval v=natCode z) :
    (rawBinaryRep P H size Q W X Y Z).eval v≠0 ↔ Codec.replacement (by omega) S n [w,x] [y,z] := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hx := valid_value (show 0<h by omega) x hH hX
  have hy := valid_value (show 0<h by omega) y hH hY
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdx : decode (show 0<h by omega) x <;>
    cases hdy : decode (show 0<h by omega) y <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawBinaryRep,branch_value,all_eval,hw,hx,hy,hz,hdw,hdx,hdy,hdz,Codec.replacement,decodeWord]
  rename_i a b c d
  have ha := rawRepresents hh w hdw hH hW
  have hb := rawRepresents hh x hdx hH hX
  have hc := rawRepresents hh y hdy hH hY
  have hd := rawRepresents hh z hdz hH hZ
  simpa [rawBinaryRep,branch_value,all_eval,hw,hx,hy,hz,hdw,hdx,hdy,hdz,
    Codec.replacement,decodeWord] using (binaryRep_exact hh P hP hs hQ ha hb hc hd)

def normalEntry (P : Table (ι:=ι)) (H size Q len zeroTask : Formula ι)
    (data : Bool → Fin 2 → Formula ι) : Formula ι :=
  .branch zeroTask
    (.branch (equal len (.constant 1)) (rawUnaryZero P H size (data false 0))
      (.branch (equal len (.constant 2)) (rawBinaryZero H Q (data false 0) (data false 1)) (.constant 0)))
    (.branch (equal len (.constant 1)) (rawUnaryRep P H size (data false 0) (data true 0))
      (.branch (equal len (.constant 2)) (rawBinaryRep P H size Q (data false 0) (data false 1) (data true 0) (data true 1)) (.constant 0)))
lemma normalEntry_zero_one {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hl : len.eval v=1) (hz : zeroTask.eval v=1)
    (hw : (data false 0).eval v=natCode w) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n true [w] []=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry,Codec.zero] using rawUnaryZero_exact hh P hP w hH hs hw
lemma normalEntry_zero_two {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} (S : Schedule (2^h))
    {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w x : Raw h) (hH : H.eval v=h) (hQ : Q.eval v=2^h) (hl : len.eval v=2) (hz : zeroTask.eval v=1)
    (hw : (data false 0).eval v=natCode w) (hx : (data false 1).eval v=natCode x) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n true [w,x] []=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry,Codec.zero] using rawBinaryZero_exact hh w x hH hQ hw hx
lemma normalEntry_rep_one {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w y : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hl : len.eval v=1) (hz : zeroTask.eval v=0)
    (hw : (data false 0).eval v=natCode w) (hy : (data true 0).eval v=natCode y) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n false [w] [y]=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry] using rawUnaryRep_exact hh P hP w y hH hs hw hy
lemma normalEntry_rep_two {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w x y z : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    (hl : len.eval v=2) (hz : zeroTask.eval v=0)
    (hw : (data false 0).eval v=natCode w) (hx : (data false 1).eval v=natCode x)
    (hy : (data true 0).eval v=natCode y) (hz' : (data true 1).eval v=natCode z) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n false [w,x] [y,z]=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry] using rawBinaryRep_exact hh P hP w x y z hH hs hQ hw hx hy hz'
omit [DecidableEq ι] in
lemma normalEntry_other (P : Table (ι:=ι)) (H size Q len zeroTask : Formula ι) (data : Bool → Fin 2 → Formula ι)
    (v : ι → ℕ) (h1 : len.eval v≠1) (h2 : len.eval v≠2) :
    (normalEntry P H size Q len zeroTask data).eval v=0 := by
  simp [normalEntry,branch_value,equal_eval,h1,h2]
end SourceBurnside.PredicateFormula

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

def totalize : Formula ι → Formula ι
  | .read i => .read i
  | .constant a => .constant a
  | .add x y => .add x.totalize y.totalize
  | .sub x y => .branch (.le y.totalize x.totalize) (.sub x.totalize y.totalize) (.constant 0)
  | .mul x y => .mul x.totalize y.totalize
  | .div x y => .branch (.le (.constant 1) y.totalize) (.div x.totalize y.totalize) (.constant 0)
  | .mod x y => .branch (.le (.constant 1) y.totalize) (.mod x.totalize y.totalize) x.totalize
  | .le x y => .le x.totalize y.totalize
  | .powTwo x => .powTwo x.totalize
  | .bitLength x => .bitLength x.totalize
  | .branch c a b => .branch (.le (.constant 1) c.totalize) a.totalize b.totalize
@[simp] theorem totalize_eval (e : Formula ι) (v : ι → ℕ) : e.totalize.eval v=e.eval v := by
  induction e with
  | read i => rfl
  | constant a => rfl
  | add x y hx hy => simp [totalize,eval,hx,hy]
  | sub x y hx hy =>
    by_cases h : y.eval v≤x.eval v
    · simp [totalize,eval,hx,hy,h]
    · simp [totalize,eval,hx,hy,h,Nat.sub_eq_zero_of_le (show x.eval v≤y.eval v by omega)]
  | mul x y hx hy => simp [totalize,eval,hx,hy]
  | div x y hx hy =>
    by_cases h : y.eval v=0
    · simp [totalize,eval,hy,h]
    · simp [totalize,eval,hx,hy,show 1≤y.eval v by omega]
  | mod x y hx hy =>
    by_cases h : y.eval v=0
    · simp [totalize,eval,hx,hy,h]
    · simp [totalize,eval,hx,hy,show 1≤y.eval v by omega]
  | le x y hx hy => simp [totalize,eval,hx,hy]
  | powTwo x hx => simp [totalize,eval,hx]
  | bitLength x hx => simp [totalize,eval,hx]
  | branch c a b hc ha hb =>
    by_cases h : c.eval v=0
    · simp [totalize,eval,hc,hb,h]
    · simp [totalize,eval,hc,ha,h,show 1≤c.eval v by omega]

def Bounded (n : ℕ) (v : ι → ℕ) : Formula ι → Prop
  | .read _ => True
  | .constant a => a.bits.length≤n
  | .add x y => x.Bounded n v ∧ y.Bounded n v ∧ x.eval v+y.eval v<2^n
  | .sub x y => x.Bounded n v ∧ y.Bounded n v
  | .mul x y => x.Bounded n v ∧ y.Bounded n v ∧ x.eval v*y.eval v<2^n
  | .div x y | .mod x y => x.Bounded n v ∧ y.Bounded n v ∧ 2*y.eval v≤2^n
  | .le x y => x.Bounded n v ∧ y.Bounded n v
  | .powTwo x => x.Bounded n v ∧ x.eval v<n
  | .bitLength x => x.Bounded n v
  | .branch c a b => c.Bounded n v ∧ (if c.eval v=0 then b.Bounded n v else a.Bounded n v)
lemma compare_boolean (x y : Formula ι) (v : ι → ℕ) : (Formula.le x y).eval v≤1 := by
  change (if x.eval v≤y.eval v then 1 else 0)≤1
  split <;> omega
lemma totalize_safe {e : Formula ι} {n : ℕ} {v : ι → ℕ} (hn : 0<n) (he : e.Bounded n v) :
    e.totalize.Safe n v := by
  have H0 : (Formula.constant 0 : Formula ι).Safe n v := by change (Nat.bits 0).length≤n;simp
  have H1 : (Formula.constant 1 : Formula ι).Safe n v := by change (Nat.bits 1).length≤n;norm_num;omega
  induction e with
  | read i => trivial
  | constant a => exact he
  | add x y hx hy => exact ⟨hx he.1,hy he.2.1,by simpa using he.2.2⟩
  | sub x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2
    refine ⟨⟨Hy,Hx⟩,compare_boolean _ _ _,?_⟩
    change (if (if y.totalize.eval v≤x.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : y.eval v≤x.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by simpa using h⟩
    · simpa only [ite_eq_right h,ite_true] using H0
  | mul x y hx hy => exact ⟨hx he.1,hy he.2.1,by simpa using he.2.2⟩
  | div x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2.1
    refine ⟨⟨H1,Hy⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1≤y.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : 1≤y.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by rw [totalize_eval];omega,by simpa using he.2.2⟩
    · simpa only [ite_eq_right h,ite_true] using H0
  | mod x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2.1
    refine ⟨⟨H1,Hy⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1≤y.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : 1≤y.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by rw [totalize_eval];omega,by simpa using he.2.2⟩
    · simpa only [ite_eq_right h,ite_true] using Hx
  | le x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,by simpa using he.2⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨⟨H1,hc he.1⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1≤c.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : c.eval v=0
    · simpa [h] using hb (by simpa only [h,ite_true] using he.2)
    · simpa only [ite_eq_left (show 1≤c.eval v by omega),Nat.one_ne_zero,ite_false] using ha (by simpa only [ite_eq_right h] using he.2)
end

section
variable {ι : Type}
lemma bounded_mono {e : Formula ι} {m n : ℕ} {v : ι → ℕ} (hmn : m≤n) (he : e.Bounded m v) :
    e.Bounded n v := by
  have hp : 2^m≤2^n := Nat.pow_le_pow_right (by omega) hmn
  induction e with
  | read i => trivial
  | constant a => exact he.trans hmn
  | add x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans_le hp⟩
  | sub x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | mul x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans_le hp⟩
  | div x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans hp⟩
  | mod x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans hp⟩
  | le x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,he.2.trans_le hmn⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    by_cases h : c.eval v=0
    · simpa only [h,ite_true] using hb (by simpa only [h,ite_true] using he.2)
    · simpa only [ite_eq_right h] using ha (by simpa only [ite_eq_right h] using he.2)

def Exponents (M : ℕ) (v : ι → ℕ) : Formula ι → Prop
  | .read _ | .constant _ => True
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .le x y => x.Exponents M v ∧ y.Exponents M v
  | .powTwo x => x.Exponents M v ∧ x.eval v≤M
  | .bitLength x => x.Exponents M v
  | .branch c a b => c.Exponents M v ∧ (if c.eval v=0 then b.Exponents M v else a.Exponents M v)
def weight : Formula ι → ℕ
  | .read _ => 1
  | .constant a => a.size+1
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .le x y => x.weight+y.weight+2
  | .powTwo x | .bitLength x => x.weight+2
  | .branch c a b => c.weight+a.weight+b.weight+2
lemma weight_pos (e : Formula ι) : 0<e.weight := by cases e <;> simp [weight]
lemma width_pos (e : Formula ι) (M : ℕ) : 0<e.weight*(M+1) := Nat.mul_pos e.weight_pos (by omega)
lemma bound_pow_mono {a b n : ℕ} (ha : a<2^b) (hb : b≤n) : a<2^n :=
  ha.trans_le (Nat.pow_le_pow_right (by omega) hb)
lemma width_binary {x y : Formula ι} (M : ℕ) :
    x.weight*(M+1)+y.weight*(M+1)+2≤(x.weight+y.weight+2)*(M+1) := by nlinarith
lemma binary_value_bound {a b A B N : ℕ} (ha : a<2^A) (hb : b<2^B) (hN : A+B+1≤N) :
    a+b<2^N ∧ a*b<2^N ∧ 2*b≤2^N := by
  have ha' : a<2^(A+B) := bound_pow_mono ha (by omega)
  have hb' : b<2^(A+B) := bound_pow_mono hb (by omega)
  have hs : a+b<2^(A+B+1) := by rw [Nat.pow_succ];omega
  have hm : a*b<2^(A+B) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  have hd : 2*b≤2^(B+1) := by rw [Nat.pow_succ];omega
  exact ⟨bound_pow_mono hs hN,bound_pow_mono hm (by omega),hd.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩

theorem bounded_of_exponents (e : Formula ι) (M : ℕ) (v : ι → ℕ)
    (hv : ∀i,v i<2^(M+1)) (he : e.Exponents M v) :
    e.Bounded (e.weight*(M+1)) v ∧ e.eval v<2^(e.weight*(M+1)) := by
  induction e with
  | read i => simpa [Bounded,weight,eval] using And.intro True.intro (hv i)
  | constant a =>
    have hw : a.size≤(a.size+1)*(M+1) := by nlinarith
    exact ⟨by change a.bits.length≤_;simpa only [Nat.size_eq_bits_len,weight] using hw,
      bound_pow_mono ((Nat.size_le).mp (le_refl a.size)) hw⟩
  | add x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.1⟩,hb.1⟩
  | sub x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,_⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy⟩,
      (Nat.sub_le _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | mul x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.1⟩,hb.2.1⟩
  | div x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.2⟩,
      (Nat.div_le_self _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | mod x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.2⟩,
      (Nat.mod_le _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | le x y hx hy =>
    obtain ⟨hx,_⟩ := hx he.1
    obtain ⟨hy,_⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    refine ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy⟩,?_⟩
    have hn := width_pos (x.le y) M
    have hpow : 1<2^((x.le y).weight*(M+1)) := Nat.one_lt_two_pow hn.ne'
    exact (compare_boolean x y v).trans_lt hpow
  | powTwo x hx =>
    obtain ⟨hx,_⟩ := hx he.1
    have hw : x.weight*(M+1)≤(x.weight+2)*(M+1) := by nlinarith
    have hM : M<(x.weight+2)*(M+1) := by nlinarith
    exact ⟨⟨bounded_mono hw hx,he.2.trans_lt hM⟩,Nat.pow_lt_pow_right (by omega) (he.2.trans_lt hM)⟩
  | bitLength x hx =>
    obtain ⟨hx,hxv⟩ := hx he
    have hw : x.weight*(M+1)≤(x.weight+2)*(M+1) := by nlinarith
    have hn := width_pos (x.bitLength) M
    refine ⟨bounded_mono hw hx,?_⟩
    have hs : (x.eval v).size≤x.weight*(M+1) := (Nat.size_le).mpr hxv
    change (if x.eval v=0 then 1 else (x.eval v).size) < _
    split
    · exact Nat.one_lt_two_pow hn.ne'
    · exact (hs.trans hw).trans_lt Nat.lt_two_pow_self
  | branch c a b hc ha hb =>
    obtain ⟨hc,_⟩ := hc he.1
    have hcN : c.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    have haN : a.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    have hbN : b.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    by_cases h : c.eval v=0
    · obtain ⟨hb,hbv⟩ := hb (by simpa [Exponents,h] using he.2)
      exact ⟨⟨bounded_mono hcN hc,by simpa only [ite_eq_left h,weight] using bounded_mono hbN hb⟩,by simpa only [eval,h,ite_true,weight] using bound_pow_mono hbv hbN⟩
    · obtain ⟨ha,hav⟩ := ha (by simpa [Exponents,h] using he.2)
      exact ⟨⟨bounded_mono hcN hc,by simpa only [ite_eq_right h,weight] using bounded_mono haN ha⟩,by simpa only [eval,ite_eq_right h,weight] using bound_pow_mono hav haN⟩
end

section
variable {ι : Type} [DecidableEq ι]

theorem timed_total (base : ι) (e : Formula ι) :
    ∃D : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀M xs,(∀i,(xs i).length=e.weight*(M+1)) →
        (∀i,values xs i<2^(M+1)) → e.Exponents M (values xs) →
        ∃t y,t≤D.coefficient*(e.weight*(M+1)+1)^2 ∧ y.length=e.weight*(M+1) ∧
          Binary.Add.value y.reverse=e.eval (values xs) ∧ Run D.program (input xs) t (result xs D.out y) := by
  refine ⟨compile base e.totalize,?_⟩
  intro M xs hl hv he
  have hB := (bounded_of_exponents e M (values xs) hv he).1
  obtain ⟨t,y,ht,hy,hv',hr⟩ := (compile base e.totalize).spec _ (width_pos e M) xs hl (totalize_safe (width_pos e M) hB)
  exact ⟨t,y,ht,hy,by simpa using hv',hr⟩
end

variable {ι κ : Type} {M : ℕ} {v : ι → ℕ}
@[simp] lemma exponents_constant (a : ℕ) : (constant a : Formula ι).Exponents M v := trivial
@[simp] lemma exponents_read (i : ι) : (read i : Formula ι).Exponents M v := trivial
lemma exponents_branch {c a b : Formula ι} (hc : c.Exponents M v)
    (ha : a.Exponents M v) (hb : b.Exponents M v) : (branch c a b).Exponents M v :=
  ⟨hc,by split <;> assumption⟩
lemma exponents_equal {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (equal a b).Exponents M v := by
  exact exponents_branch ⟨ha,hb⟩ ⟨hb,ha⟩ (exponents_constant 0)
lemma exponents_less {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (less a b).Exponents M v := by
  exact exponents_branch ⟨hb,ha⟩ (exponents_constant 0) (exponents_constant 1)
lemma exponents_neg {a : Formula ι} (ha : a.Exponents M v) : (neg a).Exponents M v :=
  exponents_branch ha (exponents_constant 0) (exponents_constant 1)
lemma exponents_and {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (and a b).Exponents M v := exponents_branch ha hb (exponents_constant 0)
lemma exponents_or {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (or a b).Exponents M v := exponents_branch ha (exponents_constant 1) hb
lemma exponents_implies {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (implies a b).Exponents M v := exponents_branch ha hb (exponents_constant 1)
lemma exponents_all {es : List (Formula ι)} (H : ∀e∈es,e.Exponents M v) : (all es).Exponents M v := by
  induction es with
  | nil => exact exponents_constant 1
  | cons e es ih => exact exponents_and (H e (by simp)) (ih (by intro a ha;exact H a (by simp [ha])))
lemma exponents_any {es : List (Formula ι)} (H : ∀e∈es,e.Exponents M v) : (any es).Exponents M v := by
  induction es with
  | nil => exact exponents_constant 0
  | cons e es ih => exact exponents_or (H e (by simp)) (ih (by intro a ha;exact H a (by simp [ha])))
lemma exponents_bit {a i : Formula ι} (hM : 1≤M) (ha : a.Exponents M v) (hi : i.Exponents M v) (hv : i.eval v≤M) :
    (bitAt a i).Exponents M v := ⟨⟨ha,hi,hv⟩,trivial,hM⟩
lemma exponents_field {a i w : Formula ι} (ha : a.Exponents M v) (hi : i.Exponents M v) (hw : w.Exponents M v)
    (hiv : i.eval v≤M) (hwv : w.eval v≤M) : (field a i w).Exponents M v := ⟨⟨ha,hi,hiv⟩,hw,hwv⟩
lemma exponents_bind (e : Formula κ) (f : κ → Formula ι)
    (hf : ∀i,(f i).Exponents M v) (he : e.Exponents M (fun i => (f i).eval v)) :
    (e.bind f).Exponents M v := by
  induction e with
  | read i => exact hf i
  | constant a => trivial
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | mod a b ha hb | le a b ha hb => exact ⟨ha he.1,hb he.2⟩
  | powTwo a ha => exact ⟨ha he.1,by simpa only [bind_eval] using he.2⟩
  | bitLength a ha => exact ha he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    simp only [bind_eval]
    split <;> rename_i h
    · exact hb (by simpa only [ite_eq_left h] using he.2)
    · exact ha (by simpa only [ite_eq_right h] using he.2)
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawFormula
open Structured.Device Structured.Device.Formula
lemma valid_exponents (h w M : ℕ) (hM : 64*h+8≤M) : valid.Exponents M (inputs h w) := by
  have Hs (i : Fin 32) : (slot i).Exponents M (inputs h w) := by
    apply exponents_field
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact ⟨trivial,trivial⟩
    · change 2*i.val*h≤M
      have := i.isLt
      nlinarith
    · change 2*h≤M
      omega
  have Hb : bound.Exponents M (inputs h w) := ⟨trivial,by simpa using (show h≤M by omega)⟩
  have Hr : ranges.Exponents M (inputs h w) := by
    apply exponents_all
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro e he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) Hb
    · exact exponents_implies (exponents_equal (Hs _) (exponents_constant _)) (exponents_equal (Hs _) (exponents_constant _))
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact ⟨Hs _,Hs _⟩
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) Hb
    · exact exponents_implies (exponents_equal (Hs _) (exponents_constant _)) (exponents_equal (Hs _) (exponents_constant _))
    · exact exponents_less (Hs _) Hb
    · exact exponents_less (Hs _) (exponents_constant _)
  apply exponents_and Hr
  apply exponents_and
  · apply exponents_equal _ (exponents_constant _)
    apply exponents_field
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact ⟨trivial,trivial⟩
    · change 18*h≤M;omega
    · change 46*h≤M;omega
  · apply exponents_equal _ (exponents_constant _)
    exact ⟨trivial,⟨⟨trivial,trivial⟩,trivial⟩,hM⟩
end SourceBurnside.RawFormula

namespace SourceBurnside.PredicateFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma valid_exponents {H W : Formula ι} (hH : H.Exponents M v) (hW : W.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (valid H W).Exponents M v := by
  apply exponents_bind
  · intro i; fin_cases i <;> assumption
  · exact RawFormula.valid_exponents _ _ _ hM
end SourceBurnside.PredicateFormula

namespace SourceBurnside.CellFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type}
def Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  (∀i,(a.1 i).Exponents M v) ∧ (∀i,(a.2 i).Exponents M v)
lemma ofRaw_exponents {H W : Formula ι} {M : ℕ} {v : ι → ℕ}
    (hH : H.Exponents M v) (hW : W.Exponents M v) (hM : 64*H.eval v+8≤M) :
    Exponents (ofRaw H W) M v := by
  constructor
  · intro i
    apply exponents_field
    · exact hW
    · exact ⟨trivial,hH⟩
    · exact ⟨trivial,hH⟩
    · change 2*i.val*H.eval v≤M
      have := i.isLt;nlinarith
    · change 2*H.eval v≤M;omega
  · intro i
    apply exponents_bit
    · omega
    · exact hW
    · exact ⟨⟨trivial,hH⟩,trivial⟩
    · change 64*H.eval v+i.val≤M
      have := i.isLt;omega
end SourceBurnside.CellFormula

namespace SourceBurnside.AddressFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) := ∀i,(a i).Exponents M v
lemma certificate_exponents {a : Formula ι} (ha : a.Exponents M v) : Exponents (certificate a) M v := by
  intro i;fin_cases i <;> simp [certificate,ha]
lemma data_exponents {s b p : Formula ι} (hs : s.Exponents M v) (hb : b.Exponents M v) (hp : p.Exponents M v) :
    Exponents (data s b p) M v := by intro i;fin_cases i <;> simp [data,hs,hb,hp]
end SourceBurnside.AddressFormula

namespace SourceBurnside.InitialFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Expr.Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  a.tag.Exponents M v ∧ AddressFormula.Exponents a.address M v ∧ a.polarity.Exponents M v
lemma fixed_exponents {b : Formula ι} (hb : b.Exponents M v) : (fixed b).Exponents M v :=
  ⟨trivial,AddressFormula.certificate_exponents trivial,hb⟩
lemma data_exponents {a : AddressFormula.Expr (ι:=ι)} {b : Formula ι}
    (ha : AddressFormula.Exponents a M v) (hb : b.Exponents M v) : (data a b).Exponents M v := ⟨trivial,ha,hb⟩
lemma choose_exponents {c : Formula ι} {a b : Expr (ι:=ι)}
    (hc : c.Exponents M v) (ha : c.eval v≠0 → a.Exponents M v) (hb : c.eval v=0 → b.Exponents M v) :
    (choose c a b).Exponents M v := by
  by_cases h : c.eval v=0
  · have hb := hb h
    refine ⟨⟨hc,?_⟩,?_,⟨hc,?_⟩⟩
    · simpa only [ite_eq_left h] using hb.1
    · intro i;exact ⟨hc,by simpa only [ite_eq_left h] using hb.2.1 i⟩
    · simpa only [ite_eq_left h] using hb.2.2
  · have ha := ha h
    refine ⟨⟨hc,?_⟩,?_,⟨hc,?_⟩⟩
    · simpa only [ite_eq_right h] using ha.1
    · intro i;exact ⟨hc,by simpa only [ite_eq_right h] using ha.2.1 i⟩
    · simpa only [ite_eq_right h] using ha.2.2
lemma symbol_exponents (f : Bool → Bool) {a : Expr (ι:=ι)} (ha : a.Exponents M v) : (symbol f a).Exponents M v := by
  unfold symbol
  split
  · exact fixed_exponents trivial
  · refine ⟨ha.1,ha.2.1,?_⟩
    split
    · exact exponents_neg ha.2.2
    · exact ha.2.2

def Piece.Exponents (p : Piece (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  p.length.Exponents M v ∧ ∀i : Formula ι,i.Exponents M v → i.eval v<p.length.eval v → (p.read i).Exponents M v
lemma Piece.append_exponents {a b : Piece (ι:=ι)} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (a.append b).Exponents M v := by
  refine ⟨⟨ha.1,hb.1⟩,?_⟩
  intro i hi hiv
  apply choose_exponents (exponents_less hi ha.1)
  · intro H
    apply ha.2 i hi
    simpa using H
  · intro H
    apply hb.2 (.sub i a.length) ⟨hi,ha.1⟩
    have H' : ¬i.eval v<a.length.eval v := by simpa using H
    change i.eval v-a.length.eval v<b.length.eval v
    change i.eval v<a.length.eval v+b.length.eval v at hiv
    omega
lemma fixedBits_exponents (bits : List Bool) (hM : 1≤M) (hlen : bits.length≤M+1) :
    (fixedBits (ι:=ι) bits).Exponents M v := by
  refine ⟨trivial,?_⟩
  intro i hi hiv
  apply fixed_exponents
  exact exponents_bit hM trivial hi (by change i.eval v<bits.length at hiv;omega)
lemma number_exponents {n : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hv : binSize (n.eval v)≤M+1) :
    (number n).Exponents M v := by
  refine ⟨hn,?_⟩
  intro i hi hiv
  apply fixed_exponents
  apply exponents_bit
  · exact hM
  · exact hn
  · exact ⟨⟨hn,trivial⟩,hi⟩
  · change binSize (n.eval v)-1-i.eval v≤M
    omega
lemma ones_exponents {n : Formula ι} (hn : n.Exponents M v) : (ones n).Exponents M v :=
  ⟨hn,fun _ _ _ => fixed_exponents trivial⟩
lemma header_exponents {n : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hv : binSize (n.eval v)≤M+1) :
    (header n).Exponents M v :=
  Piece.append_exponents (Piece.append_exponents (ones_exponents hn) (fixedBits_exponents [false] hM (by simp)))
    (number_exponents hM hn hv)
lemma bits_exponents {n len : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hl : len.Exponents M v)
    (hv : len.eval v≤M+1) : (bits n len).Exponents M v := by
  refine ⟨hl,?_⟩
  intro i hi hiv
  exact fixed_exponents (exponents_bit hM hn hi (by change i.eval v<len.eval v at hiv;omega))
lemma single_exponents {b : Formula ι} (hb : b.Exponents M v) : (single b).Exponents M v :=
  ⟨trivial,fun _ _ _ => fixed_exponents hb⟩
lemma dataPiece_exponents {d l z : Formula ι} (hd : d.Exponents M v) (hl : l.Exponents M v) (hz : z.Exponents M v) :
    (dataPiece d l z).Exponents M v := by
  refine ⟨exponents_branch hz ⟨hl,hd⟩ ⟨trivial,hl,hd⟩,?_⟩
  intro i hi hiv
  exact data_exponents (AddressFormula.data_exponents ⟨⟨hl,hd⟩,hi⟩ ⟨⟨hi,hd⟩,hl⟩ ⟨hi,hd⟩) trivial
lemma inputPiece_exponents {code len H l z : Formula ι} (hM : 1≤M)
    (hc : code.Exponents M v) (hn : len.Exponents M v) (hH : H.Exponents M v) (hl : l.Exponents M v) (hz : z.Exponents M v)
    (hlen : len.eval v≤M+1) (hlenbits : binSize (len.eval v)≤M+1)
    (hHbits : binSize (H.eval v)≤M+1) (hlbits : binSize (l.eval v)≤M+1) :
    (inputPiece code len H l z).Exponents M v := by
  apply Piece.append_exponents
  · apply Piece.append_exponents
    · apply Piece.append_exponents
      · apply Piece.append_exponents
        · exact Piece.append_exponents (header_exponents hM hn hlenbits) (bits_exponents hM hc hn hlen)
        · exact header_exponents hM hH hHbits
      · exact header_exponents hM hl hlbits
    · exact single_exponents hz
  · exact dataPiece_exponents ⟨trivial,hH⟩ hl hz

lemma cell_exponents {β : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    {o j : Formula ι} {input : Piece (ι:=ι)} (r : Fin β)
    (ho : o.Exponents M v) (hj : j.Exponents M v) (hi : input.Exponents M v) :
    (cell blank origin encoding o input j r).Exponents M v := by
  have hk : (Formula.sub j (.add o (.constant 1))).Exponents M v := ⟨hj,ho,trivial⟩
  apply choose_exponents (exponents_equal hj ho)
  · intro _;exact fixed_exponents trivial
  · intro _
    apply choose_exponents (exponents_and (exponents_less ho hj) (exponents_less hk hi.1))
    · intro H
      apply symbol_exponents
      apply hi.2 _ hk
      exact by
        have H' := ((Formula.and_ne_zero _ _ _).mp H).2
        simpa using H'
    · intro _;exact fixed_exponents trivial
end SourceBurnside.InitialFormula

namespace SourceBurnside.CellFormula
open LocalSyntax Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma equalCells_exponents {a b : Expr (ι:=ι)} (ha : Exponents a M v) (hb : Exponents b M v) :
    (equalCells a b).Exponents M v := by
  apply exponents_and
  · apply exponents_all
    simp only [List.mem_ofFn]
    rintro e ⟨i,rfl⟩
    exact exponents_equal (ha.1 _) (hb.1 _)
  · apply exponents_all
    simp only [List.mem_ofFn]
    rintro e ⟨i,rfl⟩
    exact exponents_equal (ha.2 _) (hb.2 _)
lemma wing_exponents {a : Expr (ι:=ι)} (m : Marker) (ha : Exponents a M v) : Exponents (wing a m) M v := by
  constructor <;> intro i <;> fin_cases i <;> simp [wing,ha.1,ha.2]
lemma boundary_exponents {a : Expr (ι:=ι)} {s : Formula ι} (ha : Exponents a M v) (hs : s.Exponents M v) :
    Exponents (boundary a s) M v := by
  refine ⟨(wing_exponents .boundary ha).1,?_⟩
  intro i;fin_cases i <;> simp [boundary,ha.2,hs]
lemma full_exponents {a : Expr (ι:=ι)} {s j : Formula ι} (p : FiniteTable.Phase) {r : Fin 3 → Formula ι}
    (ha : Exponents a M v) (hs : s.Exponents M v) (hj : j.Exponents M v) (hr : ∀i,(r i).Exponents M v) :
    Exponents (full a s j p r) M v := by
  constructor <;> intro i <;> fin_cases i <;> simp [full,ha.1,ha.2,hs,hj,hr]
lemma idle_exponents {a : Expr (ι:=ι)} {s : Formula ι} (ha : Exponents a M v) (hs : s.Exponents M v) :
    Exponents (idle a s) M v := by
  constructor
  · intro i;fin_cases i <;> simp [idle,ha.1]
  · intro i;fin_cases i <;> simp [idle,Formula.Exponents,hs,ha.2]
lemma setChecker_exponents {a : Expr (ι:=ι)} {tag i : Formula ι}
    (ha : Exponents a M v) (ht : tag.Exponents M v) (hi : i.Exponents M v) : Exponents (setChecker a tag i) M v := by
  refine ⟨?_,ha.2⟩
  intro j;fin_cases j <;> simp [setChecker,ha.1,ht,hi]
lemma setColor_exponents {a : Expr (ι:=ι)} {color : Formula ι}
    (ha : Exponents a M v) (hc : color.Exponents M v) : Exponents (setColor a color) M v := by
  refine ⟨?_,ha.2⟩
  intro j;fin_cases j <;> simp [setColor,ha.1,hc]
lemma formats_exponents {a : Expr (ι:=ι)} {size count : Formula ι}
    (ha : Exponents a M v) (hs : size.Exponents M v) (hc : count.Exponents M v) :
    (formats a size count).Exponents M v := by
  simp [formats,admissible,coreLimit,headZero,metaZero,dataZero,checkerIdle,regZero,
    hasHead,endpoint,hasPhase,hasMarker,first,last,isCore,isPalette,
    all,any,Formula.and,Formula.or,neg,equal,less,implies,Formula.Exponents,ha.1,ha.2,hs,hc]
lemma pair_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (pair a b Q).Exponents M v := by
  simp [pair,skeletonPair,checkerPair,palettePair,structural,internal,acceptsLeft,acceptsRight,leftExternal,rightExternal,
    checkerIdle,checkerPassed,checkerHead,hasMarker,first,last,isCore,isPalette,isStop,
    all,any,Formula.and,Formula.or,neg,equal,implies,Formula.Exponents,ha.1,ha.2,hb.1,hb.2,hQ]
lemma unaryZero_exponents {a : Expr (ι:=ι)} {size count truth : Formula ι}
    (ha : Exponents a M v) (hs : size.Exponents M v) (hc : count.Exponents M v) (ht : truth.Exponents M v) :
    (unaryZero a size count truth).Exponents M v := by
  have hf := formats_exponents ha hs hc
  simp [unaryZero,semanticZero,passedOwn,isPalette,checkerPassed,hasMarker,hasPhase,regZero,
    Formula.or,Formula.and,any,all,neg,equal,Formula.Exponents,ha.1,ha.2,hf,ht]
lemma binaryZero_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (binaryZero a b Q).Exponents M v := by
  have hp := pair_exponents ha hb hQ
  simp [binaryZero,duplicate,missing,checkerHead,isPalette,isStop,
    Formula.or,Formula.and,any,all,neg,equal,Formula.Exponents,ha.1,hb.1,hp]
end SourceBurnside.CellFormula

namespace SourceBurnside.AddressFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma readAt_exponents {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)}
    (ha : Exponents a M v) (hc : CellFormula.Exponents c M v) : (readAt a c).Exponents M v := by
  have ha' : ∀i,(a i).Exponents M v := ha
  simp [readAt,CellFormula.isCore,all,Formula.and,equal,Formula.Exponents,ha',hc.1,hc.2]
end SourceBurnside.AddressFormula

namespace SourceBurnside.ClauseFormula
open LocalSyntax FiniteTable CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Expr.Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  (∀i,AddressFormula.Exponents (a.address i) M v) ∧ (∀r,(a.truth r).Exponents M v)
lemma matchReg_exponents {r : Fin 3 → Formula ι} (hr : ∀i,(r i).Exponents M v) (R : Reg) :
    (matchReg r R).Exponents M v := by
  apply exponents_all
  simp only [List.mem_ofFn]
  rintro e ⟨i,rfl⟩
  exact exponents_equal (hr _) (exponents_constant _)
lemma truth_exponents {a : Expr (ι:=ι)} {r : Fin 3 → Formula ι}
    (ha : a.Exponents M v) (hr : ∀i,(r i).Exponents M v) : (truth a r).Exponents M v := by
  apply exponents_any
  simp only [List.mem_map]
  rintro e ⟨R,_,rfl⟩
  exact exponents_and (matchReg_exponents hr R) (ha.2 _)
lemma delta_exponents {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)} (ha : a.Exponents M v)
    (hc : CellFormula.Exponents c M v) (i : Fin 3) : (delta a c i).Exponents M v :=
  AddressFormula.readAt_exponents (ha.1 _) hc
lemma choose_exponents {c : Formula ι} {a b : Expr (ι:=ι)}
    (hc : c.Exponents M v) (ha : a.Exponents M v) (hb : b.Exponents M v) : (choose c a b).Exponents M v :=
  ⟨fun i j => exponents_branch hc (ha.1 i j) (hb.1 i j),fun r => exponents_branch hc (ha.2 r) (hb.2 r)⟩
lemma lookup_exponents {i : Formula ι} {f : Expr (ι:=ι)} {xs : List (Expr (ι:=ι))}
    (hi : i.Exponents M v) (hf : f.Exponents M v) (hx : ∀x∈xs,x.Exponents M v) (n : ℕ) :
    (lookup i f n xs).Exponents M v := by
  induction xs generalizing n with
  | nil => exact hf
  | cons x xs ih =>
    exact choose_exponents (exponents_equal hi (exponents_constant n)) (hx x (by simp))
      (ih (by intro x h;exact hx x (by simp [h])) (n+1))
lemma truthTable_exponents (f : Reg → Bool) {r : Fin 3 → Formula ι} (hr : ∀i,(r i).Exponents M v) :
    (truthTable f r).Exponents M v :=
  truth_exponents ⟨fun _ => AddressFormula.certificate_exponents trivial,fun _ => trivial⟩ hr

def ReadingExpr.Exponents (a : ReadingExpr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  AddressFormula.Exponents a.address M v ∧ ∀b,(a.value b).Exponents M v
lemma fixedReading_exponents {b : Formula ι} (hb : b.Exponents M v) : (fixedReading b).Exponents M v :=
  ⟨AddressFormula.certificate_exponents trivial,fun _ => hb⟩
lemma addressReading_exponents {a : AddressFormula.Expr (ι:=ι)} (ha : AddressFormula.Exponents a M v) :
    (addressReading a).Exponents M v := ⟨ha,fun _ => trivial⟩
lemma make_exponents {w : Fin 3 → ReadingExpr (ι:=ι)} (f : (Fin 3 → Bool) → Bool)
    (hw : ∀i,(w i).Exponents M v) : (make w f).Exponents M v :=
  ⟨fun i => (hw i).1,fun _ => truthTable_exponents _ (fun i => (hw i).2 _)⟩
lemma unit_exponents {a : ReadingExpr (ι:=ι)} {b : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) : (unit a b).Exponents M v := by
  apply choose_exponents hb <;> apply make_exponents <;> intro i <;> fin_cases i <;> exact ha
lemma equalReading_exponents {a b : ReadingExpr (ι:=ι)} {k : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) (hk : k.Exponents M v) : (equalReading a b k).Exponents M v := by
  apply choose_exponents (exponents_equal hk (exponents_constant 0)) <;> apply make_exponents <;> intro i <;> fin_cases i
  all_goals first | exact ha | exact hb
lemma initialData_exponents {a : ReadingExpr (ι:=ι)} {p : AddressFormula.Expr (ι:=ι)} {n k : Formula ι}
    (ha : a.Exponents M v) (hp : AddressFormula.Exponents p M v) (hn : n.Exponents M v) (hk : k.Exponents M v) :
    (initialData a p n k).Exponents M v := by
  apply choose_exponents hn
  · apply choose_exponents (exponents_equal hk (exponents_constant 0)) <;> apply make_exponents <;> intro i <;> fin_cases i
    all_goals first | exact ha | exact addressReading_exponents hp
  · exact equalReading_exponents ha (addressReading_exponents hp) hk
lemma wire_exponents {n : ℕ} {a : Fin n → AddressFormula.Expr (ι:=ι)}
    (ha : ∀i,AddressFormula.Exponents (a i) M v) (w : Tableau.Wire n) : (wire a w).Exponents M v := by
  cases w with
  | inl b => exact fixedReading_exponents trivial
  | inr i => exact addressReading_exponents (ha i)
lemma circuitClause_exponents {n : ℕ} {a : Fin n → AddressFormula.Expr (ι:=ι)}
    (ha : ∀i,AddressFormula.Exponents (a i) M v) (C : Tableau.Circuit.Clause n) : (circuitClause a C).Exponents M v :=
  make_exponents C.truth (fun _ => wire_exponents ha _)
end SourceBurnside.ClauseFormula

namespace SourceBurnside.InitialFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma clauses_exponents {a : ClauseFormula.ReadingExpr (ι:=ι)} {b : Expr (ι:=ι)} {k : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) (hk : k.Exponents M v) :
    (clauses a b k).Exponents M v :=
  ClauseFormula.choose_exponents hb.1 (ClauseFormula.initialData_exponents ha hb.2.1 hb.2.2 hk)
    (ClauseFormula.unit_exponents ha hb.2.2)
end SourceBurnside.InitialFormula

namespace SourceBurnside.PhysicalFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma x_exponents (β : ℕ) {W t j r : Formula ι}
    (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    AddressFormula.Exponents (x β W t j r) M v := by
  apply AddressFormula.certificate_exponents
  exact ⟨⟨trivial,⟨hW,ht⟩,hj⟩,hr⟩
lemma y_exponents (β g : ℕ) {T W t j r : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    AddressFormula.Exponents (y β g T W t j r) M v := by
  apply AddressFormula.certificate_exponents
  exact ⟨⟨⟨trivial,hW⟩,hT⟩,⟨trivial,⟨⟨hW,trivial⟩,ht⟩,hj⟩,hr⟩
lemma localAddress_exponents (β g : ℕ) {T W t j : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v)
    (i : Fin (3*β+g)) : AddressFormula.Exponents (localAddress β g T W t j i) M v := by
  refine Fin.addCases ?_ ?_ i
  · intro a;simp only [localAddress,Fin.addCases_left]
    exact x_exponents β hW ht ⟨hj,trivial⟩ trivial
  · intro a;simp only [localAddress,Fin.addCases_right]
    exact y_exponents β g hT hW ht hj trivial
lemma localClause_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) {T W t j i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hi : i.Exponents M v) :
    (localClause β g c output T W t j i).Exponents M v := by
  have hf : (ClauseFormula.unit (ι:=ι) (ClauseFormula.fixedReading (.constant 1)) (.constant 1)).Exponents M v :=
    ClauseFormula.unit_exponents (ClauseFormula.fixedReading_exponents trivial) trivial
  have ha := localAddress_exponents β g hT hW ht hj
  apply ClauseFormula.choose_exponents (exponents_less hi (exponents_constant _))
  · apply ClauseFormula.lookup_exponents hi hf
    simp only [List.mem_map]
    rintro e ⟨C,_,rfl⟩
    exact ClauseFormula.circuitClause_exponents ha C
  · apply ClauseFormula.lookup_exponents (by exact ⟨⟨hi,trivial⟩,trivial⟩) hf
    simp only [List.mem_ofFn]
    rintro e ⟨r,rfl⟩
    exact ClauseFormula.equalReading_exponents
      (ClauseFormula.addressReading_exponents (x_exponents β hW ⟨ht,trivial⟩ ⟨hj,trivial⟩ trivial))
      (ClauseFormula.wire_exponents ha _) ⟨⟨hi,trivial⟩,trivial⟩
lemma clauseIndex_exponents (β g : ℕ) {T W i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hi : i.Exponents M v) (j : Fin 4) :
    (clauseIndex β g T W i j).Exponents M v := by
  fin_cases j <;> simp [clauseIndex,chooseIndex,less,Formula.Exponents,hT,hW,hi]
lemma fallback_exponents : (fallback (ι:=ι)).Exponents M v :=
  ClauseFormula.unit_exponents (ClauseFormula.fixedReading_exponents trivial) trivial
lemma initialFamily_exponents (β : ℕ) {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {W j r k : Formula ι}
    (hW : W.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) (hk : k.Exponents M v)
    (hinit : ∀s,(init j s).Exponents M v) : (initialFamily β init W j r k).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  exact InitialFormula.clauses_exponents (ClauseFormula.addressReading_exponents (x_exponents β hW trivial hj trivial)) (hinit s) hk
lemma boundaryFamily_exponents (β : ℕ) (blank : Fin β → Bool) {W t j r : Formula ι}
    (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    (boundaryFamily β blank W t j r).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  apply ClauseFormula.unit_exponents
  · apply ClauseFormula.addressReading_exponents
    apply x_exponents
    · exact hW
    · exact ⟨ht,trivial⟩
    · exact exponents_branch (exponents_equal hj (exponents_constant 0)) trivial ⟨hW,trivial⟩
    · trivial
  · trivial
lemma finalFamily_exponents (β : ℕ) (accept : Fin β → Bool) {T W O r : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (hr : r.Exponents M v) :
    (finalFamily β accept T W O r).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  exact ClauseFormula.unit_exponents (ClauseFormula.addressReading_exponents (x_exponents β hW ⟨hT,trivial⟩ hO trivial)) trivial
lemma familyClause_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} (blank accept : Fin β → Bool) {T W O : Formula ι} {e : Fin 4 → Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (he : ∀i,(e i).Exponents M v)
    (hinit : ∀j,j.Exponents M v → ∀r,(init j r).Exponents M v) :
    (familyClause β g c output init blank accept T W O e).Exponents M v := by
  apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 0))
  · exact initialFamily_exponents β hW (he _) (he _) (he _) (hinit _ (he _))
  · apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 1))
    · exact boundaryFamily_exponents β blank hW (he _) (he _) (he _)
    · apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 2))
      · exact localClause_exponents β g c output hT hW (he _) (he _) (he _)
      · exact finalFamily_exponents β accept hT hW hO (he _)
lemma clauseAt_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} (blank accept : Fin β → Bool) {T W O i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (hi : i.Exponents M v)
    (hinit : ∀j,j.Exponents M v → ∀r,(init j r).Exponents M v) :
    (clauseAt β g c output init blank accept T W O i).Exponents M v :=
  familyClause_exponents β g c output blank accept hT hW hO (clauseIndex_exponents β g hT hW hi) hinit
end SourceBurnside.PhysicalFormula

namespace SourceBurnside.CellFormula
open LocalSyntax Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma skeletonPair_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (skeletonPair a b Q).Exponents M v := by
  simp [skeletonPair,structural,internal,acceptsLeft,acceptsRight,leftExternal,rightExternal,
    hasMarker,first,last,isCore,isPalette,isStop,all,any,Formula.and,Formula.or,neg,equal,
    Formula.Exponents,ha.1,ha.2,hb.1,hb.2,hQ]
lemma register_exponents {a : Expr (ι:=ι)} (ha : Exponents a M v) (i : Fin 3) :
    (register a i).Exponents M v := ha.2 _
lemma zeroReg_exponents (i : Fin 3) : (zeroReg (ι:=ι) i).Exponents M v := trivial
attribute [local simp] register_exponents zeroReg_exponents equalCells_exponents wing_exponents boundary_exponents full_exponents
  idle_exponents setChecker_exponents setColor_exponents skeletonPair_exponents
lemma unaryMove_exponents {a b : Expr (ι:=ι)} {count truth : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v)
    (hc : count.Exponents M v) (ht : truth.Exponents M v) :
    (unaryMove a b count truth).Exponents M v := by
  have hra := register_exponents ha
  have hrb := register_exponents hb
  have hz : ∀ i, (zeroReg (ι:=ι) i).Exponents M v := zeroReg_exponents
  have h0 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (exponents_constant 0) hz
  have h1 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (hb.1 7) hrb
  have h2 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (ha.1 7) hz
  have h3 (p : FiniteTable.Phase) := full_exponents p hb (exponents_neg (hb.2 1)) (exponents_constant 0) hz
  simp [unaryMove,all,any,Formula.and,Formula.or,equal,first,last,side,clause,
    Formula.Exponents,ha,hb,ha.1,hb.1,hb.2,hc,ht,hz,h0,h1,h2,h3]
lemma addReg_exponents {r t : Fin 3 → Formula ι}
    (hr : ∀i,(r i).Exponents M v) (ht : ∀i,(t i).Exponents M v) (i : Fin 3) :
    (addReg r t i).Exponents M v := by simp [addReg,Formula.Exponents,hr,ht]
attribute [local simp] addReg_exponents
lemma binaryMove_exponents {a b a' b' : Expr (ι:=ι)} {Q : Formula ι}
    {readDelta undoDelta : Fin 3 → Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v)
    (ha' : Exponents a' M v) (hb' : Exponents b' M v) (hQ : Q.Exponents M v)
    (hr : ∀i,(readDelta i).Exponents M v) (hu : ∀i,(undoDelta i).Exponents M v) :
    (binaryMove a b a' b' Q readDelta undoDelta).Exponents M v := by
  have hra := register_exponents ha
  have hrb := register_exponents hb
  have hread := addReg_exponents hrb hr
  have hundo := addReg_exponents hra hu
  have h0 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (hb.1 7) hrb
  have h1 (p : FiniteTable.Phase) := full_exponents p ha (hb.2 1) (hb.1 7) hread
  have h2 (p : FiniteTable.Phase) := full_exponents p ha (ha.2 1) (ha.1 7) hra
  have h3 (p : FiniteTable.Phase) := full_exponents p hb (ha.2 1) (ha.1 7) hra
  have h4 (p : FiniteTable.Phase) := full_exponents p ha (hb.2 1) (hb.1 7) hrb
  have h5 (p : FiniteTable.Phase) := full_exponents p hb (ha.2 1) (ha.1 7) hundo
  have hk0 := setChecker_exponents ha (exponents_constant 1) (ha.1 6)
  have hk1 := setChecker_exponents hb (exponents_constant 2) (ha.1 6)
  have hk2 := setChecker_exponents hb' (exponents_constant 0) (exponents_constant 0)
  simp [binaryMove,acquireMove,readLeftMove,readRightMove,undoLeftMove,undoRightMove,
    checkerCreateMove,checkerAdvanceMove,swapMove,all,any,Formula.and,Formula.or,equal,
    side,clause,isCore,isPalette,checkerHead,checkerIdle,headFree,hasHead,hasMarker,
    Formula.Exponents,ha,hb,ha',hb',ha.1,ha.2,hb.1,hb'.1,hQ,h0,h1,h2,h3,h4,h5,hk0,hk1,hk2]
  all_goals simp [neg,Formula.Exponents,ha.1,hb.1]
end SourceBurnside.CellFormula

namespace SourceBurnside.InitialFormula
lemma binSize_le_self (n : ℕ) : binSize n ≤ n+1 := by
  unfold binSize
  split
  · omega
  · apply Nat.size_le.mpr
    exact (Nat.lt_succ_self n).trans Nat.lt_two_pow_self
end SourceBurnside.InitialFormula
namespace SourceBurnside.CellFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Ready (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  Exponents a M v ∧ InitialFormula.binSize ((a.1 3).eval v+1)≤M+1
lemma ofRaw_ready {H W : Formula ι}
    (hH : H.Exponents M v) (hW : W.Exponents M v) (hM : 64*H.eval v+8≤M) :
    Ready (ofRaw H W) M v := by
  refine ⟨ofRaw_exponents hH hW hM,?_⟩
  have hlt : ((ofRaw H W).1 3).eval v<2^(2*H.eval v) := by
    change W.eval v / 2^(6*H.eval v) % 2^(2*H.eval v)<2^(2*H.eval v)
    exact Nat.mod_lt _ (by positivity)
  have hs := Nat.size_le_size (show ((ofRaw H W).1 3).eval v+1≤2^(2*H.eval v) by omega)
  rw [Nat.size_pow] at hs
  simp only [InitialFormula.binSize,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
  omega
end SourceBurnside.CellFormula

namespace SourceBurnside.PredicateFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Table.Exponents (P : Table (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  ∀a, CellFormula.Ready a M v → (P.count a).Exponents M v ∧
    ∀j,j.Exponents M v → (P.clause a j).Exponents M v
lemma Table.truth_exponents {P : Table (ι:=ι)} (hP : P.Exponents M v)
    {a : CellFormula.Expr (ι:=ι)} (ha : CellFormula.Ready a M v) : (P.truth a).Exponents M v :=
  ClauseFormula.truth_exponents ((hP a ha).2 _ (ha.1.1 _)) (fun _ => ha.1.2 _)
lemma Table.delta_exponents {P : Table (ι:=ι)} (hP : P.Exponents M v)
    {a b : CellFormula.Expr (ι:=ι)} (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v) (i : Fin 3) :
    (P.delta a b i).Exponents M v :=
  ClauseFormula.delta_exponents ((hP a ha).2 _ (hb.1.1 _)) ha.1 i
lemma clauseCount_exponents (β g : ℕ) {T W : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) : (clauseCount β g T W).Exponents M v := by
  simp [clauseCount,Formula.Exponents,hT,hW]
lemma physical_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) (blank origin accept : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) {T W O code codeLength H : Formula ι}
    (hM : 1≤M) (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v)
    (hcode : code.Exponents M v) (hlen : codeLength.Exponents M v) (hH : H.Exponents M v)
    (hlenv : codeLength.eval v≤M) (hHv : H.eval v≤M) :
    (physical β g c output blank origin accept encoding T W O code codeLength H).Exponents M v := by
  intro a ha
  have hc := clauseCount_exponents β g hT hW
  refine ⟨hc,?_⟩
  intro j hj
  apply ClauseFormula.choose_exponents (exponents_less hj hc)
  · apply PhysicalFormula.clauseAt_exponents β g c output blank accept hT hW hO hj
    intro k hk r
    apply InitialFormula.cell_exponents blank origin encoding r hO hk
    apply InitialFormula.inputPiece_exponents hM hcode hlen hH
    · exact ⟨ha.1.1 _,trivial⟩
    · exact ha.1.2 _
    · omega
    · exact (InitialFormula.binSize_le_self _).trans (by omega)
    · exact (InitialFormula.binSize_le_self _).trans (by omega)
    · exact ha.2
  · exact PhysicalFormula.fallback_exponents
lemma unaryRep_exponents {P : Table (ι:=ι)} {size : Formula ι} {a b : CellFormula.Expr (ι:=ι)}
    (hP : P.Exponents M v) (hs : size.Exponents M v)
    (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v) :
    (unaryRep P size a b).Exponents M v := by
  apply exponents_all
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl|rfl|rfl
  · exact CellFormula.formats_exponents ha.1 hs (hP a ha).1
  · exact CellFormula.formats_exponents hb.1 hs (hP b hb).1
  · exact exponents_or (CellFormula.unaryMove_exponents ha.1 hb.1 (hP b hb).1 (Table.truth_exponents hP hb))
      (CellFormula.unaryMove_exponents hb.1 ha.1 (hP a ha).1 (Table.truth_exponents hP ha))
lemma binaryRep_exponents {P : Table (ι:=ι)} {size Q : Formula ι} {a b a' b' : CellFormula.Expr (ι:=ι)}
    (hP : P.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v)
    (ha' : CellFormula.Ready a' M v) (hb' : CellFormula.Ready b' M v) :
    (binaryRep P size Q a b a' b').Exponents M v := by
  apply exponents_all
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl|rfl|rfl|rfl|rfl
  · exact CellFormula.formats_exponents ha.1 hs (hP a ha).1
  · exact CellFormula.formats_exponents hb.1 hs (hP b hb).1
  · exact CellFormula.formats_exponents ha'.1 hs (hP a' ha').1
  · exact CellFormula.formats_exponents hb'.1 hs (hP b' hb').1
  · exact exponents_or (CellFormula.binaryMove_exponents ha.1 hb.1 ha'.1 hb'.1 hQ
        (Table.delta_exponents hP ha hb) (Table.delta_exponents hP ha ha))
      (CellFormula.binaryMove_exponents ha'.1 hb'.1 ha.1 hb.1 hQ
        (Table.delta_exponents hP ha' hb') (Table.delta_exponents hP ha' ha'))
end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma rawUnaryZero_exponents {P : Table (ι:=ι)} {H size W : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hW : W.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawUnaryZero P H size W).Exponents M v := by
  have ha := CellFormula.ofRaw_ready hH hW hM
  exact exponents_branch (valid_exponents hH hW hM)
    (CellFormula.unaryZero_exponents ha.1 hs (hP _ ha).1 (Table.truth_exponents hP ha)) trivial
lemma rawBinaryZero_exponents {H Q W Z : Formula ι}
    (hH : H.Exponents M v) (hQ : Q.Exponents M v) (hW : W.Exponents M v) (hZ : Z.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawBinaryZero H Q W Z).Exponents M v :=
  exponents_branch (exponents_and (valid_exponents hH hW hM) (valid_exponents hH hZ hM))
    (CellFormula.binaryZero_exponents (CellFormula.ofRaw_exponents hH hW hM)
      (CellFormula.ofRaw_exponents hH hZ hM) hQ) trivial
lemma rawUnaryRep_exponents {P : Table (ι:=ι)} {H size W Z : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v)
    (hW : W.Exponents M v) (hZ : Z.Exponents M v) (hM : 64*H.eval v+8≤M) :
    (rawUnaryRep P H size W Z).Exponents M v :=
  exponents_branch (exponents_and (valid_exponents hH hW hM) (valid_exponents hH hZ hM))
    (unaryRep_exponents hP hs (CellFormula.ofRaw_ready hH hW hM) (CellFormula.ofRaw_ready hH hZ hM)) trivial
lemma rawBinaryRep_exponents {P : Table (ι:=ι)} {H size Q W X Y Z : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (hW : W.Exponents M v) (hX : X.Exponents M v) (hY : Y.Exponents M v) (hZ : Z.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawBinaryRep P H size Q W X Y Z).Exponents M v := by
  apply exponents_branch
  · apply exponents_all
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro e he;rcases he with rfl|rfl|rfl|rfl
    · exact valid_exponents hH hW hM
    · exact valid_exponents hH hX hM
    · exact valid_exponents hH hY hM
    · exact valid_exponents hH hZ hM
  · exact binaryRep_exponents hP hs hQ (CellFormula.ofRaw_ready hH hW hM) (CellFormula.ofRaw_ready hH hX hM)
      (CellFormula.ofRaw_ready hH hY hM) (CellFormula.ofRaw_ready hH hZ hM)
  · trivial
lemma normalEntry_exponents {P : Table (ι:=ι)} {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (hl : len.Exponents M v) (hz : zeroTask.Exponents M v) (hd : ∀b i,(data b i).Exponents M v)
    (hM : 64*H.eval v+8≤M) : (normalEntry P H size Q len zeroTask data).Exponents M v := by
  apply exponents_branch hz
  · apply exponents_branch (exponents_equal hl (exponents_constant 1))
    · exact rawUnaryZero_exponents hP hH hs (hd _ _) hM
    · exact exponents_branch (exponents_equal hl (exponents_constant 2))
        (rawBinaryZero_exponents hH hQ (hd _ _) (hd _ _) hM) trivial
  · apply exponents_branch (exponents_equal hl (exponents_constant 1))
    · exact rawUnaryRep_exponents hP hH hs (hd _ _) (hd _ _) hM
    · exact exponents_branch (exponents_equal hl (exponents_constant 2))
        (rawBinaryRep_exponents hP hH hs hQ (hd _ _) (hd _ _) (hd _ _) (hd _ _) hM) trivial
end SourceBurnside.PredicateFormula

namespace SourceBurnside.Structured.Device
open Binary

def packed (n a : ℕ) : List Bool := List.replicate (n-a.bits.length) false++a.bits.reverse
lemma packed_length (n a : ℕ) (ha : a<2^n) : (packed n a).length=n := by
  have H : a.bits.length≤n := by rw [Nat.size_eq_bits_len];exact Nat.size_le.mpr ha
  simp [packed];omega
lemma packed_value (n a : ℕ) : Add.value (packed n a).reverse=a := by
  simp [packed,List.reverse_append,Add.value_append,Constant.value_false,Constant.value_bits]

def packedInputs {ι : Type} (n : ℕ) (vs : ι → ℕ) : ι → List Bool := fun i => packed n (vs i)
@[simp] lemma packedInputs_values {ι : Type} (n : ℕ) (vs : ι → ℕ) : values (packedInputs n vs)=vs := by
  funext i;exact packed_value n (vs i)
lemma packedInputs_lengths {ι : Type} (n : ℕ) (vs : ι → ℕ) (hs : ∀i,vs i<2^n) :
    ∀i,(packedInputs n vs i).length=n := fun i => packed_length n (vs i) (hs i)

end SourceBurnside.Structured.Device

end OAI
