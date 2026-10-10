import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanRecode
import OAI.Combinatorics.KMedian.Binary.BinaryWords

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem normalize_length (xs : List Bool) : (normalize xs).length≤xs.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not xs.reverse

 theorem bits_value_length (xs : List Bool) : (value xs).bits.length≤xs.length := by
  rw [← normalize_eq_bits]
  exact normalize_length xs
end Word

namespace NatBinary
 theorem zero_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := Word.value_bits n
    rw [h,Word.value_nil] at hv
    exact hv.symm
  · rintro rfl; rfl

 theorem bit_length (b : Bool) (n : ℕ) : (Nat.bit b n).bits.length≤n.bits.length+1 := by
  have h := Word.bits_value_length (b::n.bits)
  simpa only [Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm,List.length_cons] using h

 theorem half_length (n : ℕ) : n.div2.bits.length=n.bits.length-1 := by
  rw [Nat.div2_bits_eq_tail,List.length_tail]

 theorem add_length (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_right a.size b.size))
  rw [pow_succ]
  omega

 theorem mul_length (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  rw [pow_add]
  nlinarith

 theorem length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

 theorem half_lt_length {n : ℕ} (hn : n≠0) : n.div2.bits.length<n.bits.length := by
  rw [half_length]
  have hh : n.bits≠[] := fun h => hn ((zero_iff n).mp h)
  have hl : 0<n.bits.length := List.length_pos_iff.mpr hh
  omega
end NatBinary

namespace PolyProgram
noncomputable def natBit : PolyProgram (encodePair encodeBool Nat.bits) Nat.bits (fun x : Bool × ℕ => Nat.bit x.1 x.2) :=
  (cons.comp toBits).recode (fun x => (x.1,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm])

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

noncomputable def natOdd : PolyProgram Nat.bits encodeBool Nat.bodd :=
  head.recode Nat.bits (fun _ => rfl) (fun n => by
    rw [Nat.bodd_eq_bits_head]
    cases n.bits <;> rfl)

noncomputable def natZero : PolyProgram Nat.bits encodeBool (fun n => decide (n=0)) :=
  isEmpty.recode Nat.bits (fun _ => rfl) (fun n => by
    congr 1
    cases h : n.bits.isEmpty
    · have hn : n≠0 := by intro hn; subst n; contradiction
      exact (decide_eq_false hn).symm
    · have hn : n=0 := (NatBinary.zero_iff n).mp (List.isEmpty_iff.mp h)
      exact (decide_eq_true hn).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
