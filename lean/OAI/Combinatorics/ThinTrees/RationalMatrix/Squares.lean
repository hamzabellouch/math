import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.BitSupport
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization

namespace OAI

/-! Rational squares. -/

section

namespace AlgorithmicThinTrees.RationalGram
open CurrentKS.RationalBits

def base4Squares : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1,n => List.replicate (n%4) 1 ++ (base4Squares k (n/4)).map (2*·)

lemma base4Squares_sum (k n : ℕ) (hn : n < 4^k) :
    ((base4Squares k n).map (·^2)).sum = n := by
  induction k generalizing n with
  | zero =>
    have hz : n=0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    have hn' : n/4 < 4^k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hn)
    have hsum : ((base4Squares k (n/4)).map (fun a => (2*a)^2)).sum =
        4*((base4Squares k (n/4)).map (fun a => a^2)).sum := by
      rw [← List.sum_map_mul_left]
      congr 2
      funext a
      ring
    simp only [base4Squares,List.map_append,List.map_replicate,one_pow,
      List.map_map,Function.comp_def,List.sum_append,List.sum_replicate,nsmul_eq_mul,mul_one]
    rw [hsum,ih _ hn']
    exact Nat.mod_add_div n 4

lemma base4Squares_length (k n : ℕ) : (base4Squares k n).length ≤ 3*k := by
  induction k generalizing n with
  | zero => simp [base4Squares]
  | succ k ih =>
    simp only [base4Squares,List.length_append,List.length_replicate,List.length_map]
    have hh := ih (n/4)
    have hd := Nat.mod_lt n (by decide : 0<4)
    omega

lemma base4Squares_entry (k n a : ℕ) (ha : a ∈ base4Squares k n) : a ≤ 2^k := by
  induction k generalizing n a with
  | zero => simp [base4Squares] at ha
  | succ k ih =>
    simp only [base4Squares,List.mem_append,List.mem_replicate,List.mem_map] at ha
    rcases ha with ⟨_,rfl⟩|⟨v,hv,rfl⟩
    · exact Nat.one_le_two_pow
    · rw [pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 (ih (n/4) v hv)

def scalarFactors (q : ℚ) : List ℚ :=
  let n := q.num.natAbs*q.den
  (base4Squares n.size n).map (fun a : ℕ => (a:ℚ)/q.den)

lemma scalarFactors_zero : scalarFactors 0=[] := by simp [scalarFactors,base4Squares]

lemma scalarFactors_sum (q : ℚ) (hq : 0 ≤ q) :
    ((scalarFactors q).map (·^2)).sum=q := by
  let n := q.num.natAbs*q.den
  have hn : n < 4^n.size := (Nat.lt_size_self n).trans_le
    (Nat.pow_le_pow_left (by decide : 2≤4) _)
  have hh := base4Squares_sum n.size n hn
  have hcast : ((base4Squares n.size n).map (fun a : ℕ => (a:ℚ)^2)).sum=(n:ℚ) := by
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_pow] using
      congrArg (fun a : ℕ => (a:ℚ)) hh
  have hden : (q.den:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hnum : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun a : ℤ => (a:ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq))
  simp only [scalarFactors,List.map_map,Function.comp_def,div_pow]
  change ((base4Squares n.size n).map (fun a : ℕ => (a:ℚ)^2/(q.den:ℚ)^2)).sum=q
  simp_rw [div_eq_mul_inv]
  rw [List.sum_map_mul_right,hcast,←div_eq_mul_inv]
  dsimp [n]
  push_cast
  rw [hnum]
  rw [show (q.num:ℚ)*(q.den:ℚ)/(q.den:ℚ)^2 = (q.num:ℚ)/q.den by field_simp]
  exact Rat.num_div_den q

lemma product_size {q : ℚ} {b : ℕ} (hq : Parts b q) :
    (q.num.natAbs*q.den).size ≤ 2*b+1 := by
  have h := Nat.mul_le_mul hq.1 hq.2
  rw [← pow_add] at h
  simpa only [Nat.size_pow,two_mul] using Nat.size_le_size h

lemma scalarFactors_length {q : ℚ} {b : ℕ} (hq : Parts b q) :
    (scalarFactors q).length ≤ 3*(2*b+1) := by
  rw [scalarFactors,List.length_map]
  exact (base4Squares_length _ _).trans (Nat.mul_le_mul_left 3 (product_size hq))

lemma scalarFactors_parts {q : ℚ} {b : ℕ} (hq : Parts b q)
    {v : ℚ} (hv : v ∈ scalarFactors q) : Parts (3*b+1) v := by
  rcases List.mem_map.mp hv with ⟨a,ha,rfl⟩
  have hanum := base4Squares_entry _ _ a ha
  have hb := product_size hq
  have hp : Parts (2*b+1) (a:ℚ) := by
    constructor
    · simpa using hanum.trans (Nat.pow_le_pow_right (by decide) hb)
    · simp [Nat.one_le_two_pow]
  have hd : Parts b (q.den:ℚ) := by
    constructor
    · simpa using hq.2
    · simp [Nat.one_le_two_pow]
  convert hp.div hd using 1
  omega

end AlgorithmicThinTrees.RationalGram
end

end OAI
