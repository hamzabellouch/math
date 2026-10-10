import OAI.NumberTheory.TwoPoint.Circuits.CircuitAndCertificate

namespace OAI

/-! The OR step uses complementary child polynomials and the same Boolean
error certificates. Both polarities therefore admit the same recursive bounds. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def CircuitCertificate.orGate {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n)
    (H : ∀ i, CircuitCertificate ν s (c i)) :
    CircuitCertificate ν s (.orGate c) := by
  let P := fun i x => 1 - (H i).polynomial x
  let E := fun i => (H i).error
  let c' := fun i => (c i).negate
  have hcorrect (i : Fin k) (x : BooleanCube n) (hx : (E i).eval x ≠ true) :
      P i x = (c' i).indicator x := by
    change 1 - (H i).polynomial x = (c i).negate.indicator x
    rw [(H i).exact_off_error x hx, AC0Circuit.negate_indicator]
  let hs := exists_certified_and_sample ν s c' E P
    (fun i => ((c i).size : ℝ) * (7 / 8 : ℝ) ^ s)
    (fun i => (H i).error_probability) hcorrect
  let sample := Classical.choose hs
  have hprob := (Classical.choose_spec hs).1
  have hexact := (Classical.choose_spec hs).2
  refine
    { polynomial := fun x => 1 - sampledAndPolynomial sample (fun i => P i x)
      error := AC0Circuit.combineGateException sample c' E
      degree_bound := ?_
      error_depth := ?_
      error_size := ?_
      error_probability := ?_
      exact_off_error := ?_
      norm_bound := ?_ }
  · let d := univ.sup (fun i => (c i).approximationDegree s)
    have hP (i : Fin k) : WalshDegreeLE (P i) d :=
      (WalshDegreeLE.const 1 d).sub ((H i).degree_bound.mono
        (le_sup (f := fun j => (c j).approximationDegree s) (mem_univ i)))
    exact (WalshDegreeLE.const 1 _).sub (sampledAndPolynomial_degree sample P d hP)
  · let D := univ.sup (fun i => (c i).depth)
    have hc (i : Fin k) : (c' i).depth ≤ D := by
      simpa only [c', AC0Circuit.negate_depth] using
        (le_sup (f := fun j => (c j).depth) (mem_univ i))
    have hE (i : Fin k) : (E i).depth ≤ 4 * D + 4 := by
      have hh := (H i).error_depth
      have hd := le_sup (f := fun j => (c j).depth) (mem_univ i)
      change (H i).error.depth ≤ 4 * D + 4
      omega
    have hh := AC0Circuit.combineGateException_depth sample c' E hc hE (by omega)
    change (AC0Circuit.combineGateException sample c' E).depth ≤ 4 * (1 + D) + 1
    omega
  · rw [AC0Circuit.combineGateException_size]
    have hs := AC0Circuit.gateSamplingException_size sample c'
    simp only [c', AC0Circuit.negate_size] at hs
    have he : ∑ i, (E i).size ≤ ∑ i, (c i).exceptionSizeBound s :=
      sum_le_sum (fun i _ => (H i).error_size)
    change 1 + (AC0Circuit.gateSamplingException sample c').size + ∑ i, (E i).size ≤
      4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s
    dsimp only [c']
    omega
  · convert hprob using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]
  · intro x hx
    have hh := hexact x hx
    change 1 - sampledAndPolynomial sample (fun i => P i x) = _
    rw [hh]
    have he := AC0Circuit.negate_indicator (.orGate c) x
    change (AC0Circuit.andGate c').indicator x = 1 - (AC0Circuit.orGate c).indicator x at he
    rw [he]
    ring
  · intro x
    let B := ∑ i, (c i).sampleNormBound s
    have hB : 0 ≤ B := sum_nonneg (fun i _ => AC0Circuit.sampleNormBound_nonneg s (c i))
    have hP (i : Fin k) : |P i x| ≤ 1 + B := by
      have hi : |(H i).polynomial x| ≤ B :=
        ((H i).norm_bound x).trans
          (single_le_sum (fun j _ => AC0Circuit.sampleNormBound_nonneg s (c j)) (mem_univ i))
      exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) hi)
    have hb := sampledAndPolynomial_abs_le sample (fun i => P i x) (by positivity : 0 ≤ 1 + B) hP
    have hbase : 1 + (k : ℝ) * (1 + (1 + B)) = 1 + (k : ℝ) * (2 + B) := by ring
    rw [hbase] at hb
    change |1 - sampledAndPolynomial sample (fun i => P i x)| ≤
      1 + (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3))
    exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) hb)

noncomputable def AC0Circuit.certificate {n : ℕ} (ν : FiniteLaw (BooleanCube n))
    (s : ℕ) (c : AC0Circuit n) : CircuitCertificate ν s c := by
  induction c with
  | literal i b => exact CircuitCertificate.literal ν s i b
  | andGate c ih => exact CircuitCertificate.andGate ν s c ih
  | orGate c ih => exact CircuitCertificate.orGate ν s c ih

end TwoPointCorrelations

end OAI
