import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulus
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesPrecision

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction

def factorBound (N : ℕ) (B : ℝ) : {l : ℕ} → History l → Prop
  | _,.leaf a => |(a.frequency:ℝ)|≤B ∧ a.small.length≤N ∧ ∀q∈a.small,(q.value:ℝ)≤B
  | _,.node a _ u _ _ left right =>
      |(a.frequency:ℝ)|≤B ∧ a.small.length≤N ∧ (∀q∈a.small,(q.value:ℝ)≤B) ∧
      u.length≤N ∧ (∀q∈u,(q.value:ℝ)≤B) ∧ factorBound N B left ∧ factorBound N B right

def divisorCost : {l : ℕ} → History l → ℕ
  | _,.leaf _ => 0
  | _,.node _ _ u _ _ left right => 1+u.length+divisorCost left+divisorCost right

def testCost : {l : ℕ} → History l → ℕ
  | _,.leaf a => 1+a.small.length
  | _,h@(.node a _ u _ _ left right) =>
      h.frequencies.length+a.small.length+1+3*u.length+testCost left+testCost right

def intSize (z : ℤ) : ℝ := |(z:ℝ)|

@[simp] lemma intSize_mul (z w : ℤ) : intSize (z*w)=intSize z*intSize w := by
  simp only [intSize,Int.cast_mul,abs_mul]
@[simp] lemma intSize_pow (z : ℤ) (n : ℕ) : intSize (z^n)=intSize z^n := by
  simp only [intSize,Int.cast_pow,abs_pow]
lemma intSize_nonneg (z : ℤ) : 0 ≤ intSize z := abs_nonneg _

lemma intSize_list_prod_le {B : ℝ} (hB:0≤B) (xs : List ℤ)
    (hx : ∀z∈xs,intSize z≤B) : intSize xs.prod≤B^xs.length := by
  induction xs with
  | nil => simp [intSize]
  | cons z zs ih =>
    simp only [List.prod_cons,List.length_cons,intSize_mul]
    simpa only [pow_succ,mul_comm] using mul_le_mul (hx z (List.mem_cons_self))
      (ih (fun w hw => hx w (List.mem_cons_of_mem z hw))) (intSize_nonneg _) hB

lemma smallProduct_intSize_le {B : ℝ} (hB:0≤B) (xs : List SmallSlot)
    (hx : ∀q∈xs,(q.value:ℝ)≤B) :
    intSize ((xs.map SmallSlot.value).prod:ℤ)≤B^xs.length := by
  induction xs with
  | nil => simp [intSize]
  | cons z zs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,Nat.cast_mul,intSize_mul]
    have hz : intSize (z.value:ℤ)≤B := by
      simpa only [intSize,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg z.value : (0:ℝ)≤(z.value:ℝ))] using hx z List.mem_cons_self
    simpa only [pow_succ,mul_comm] using mul_le_mul hz
      (ih (fun q hq => hx q (List.mem_cons_of_mem z hq))) (intSize_nonneg _) hB

lemma factorBound_frequencies {N : ℕ} {B : ℝ} {l : ℕ} (h : History l)
    (hb : factorBound N B h) : ∀v∈h.frequencies,intSize v≤B := by
  induction h with
  | leaf a =>
    intro v hv
    have he : v=a.frequency := by simpa only [History.frequencies,List.mem_singleton] using hv
    subst v
    exact hb.1
  | node a p u hp hm left right il ir =>
    intro v hv
    rcases List.mem_cons.mp hv with he|hv
    · subst v; exact hb.1
    · rcases List.mem_append.mp hv with hv|hv
      · exact il hb.2.2.2.2.2.1 v hv
      · exact ir hb.2.2.2.2.2.2 v hv

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
