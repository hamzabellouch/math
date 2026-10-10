import OAI.NumberTheory.TwoPoint.Circuits.CircuitCertificateBounds

namespace OAI

/-! An AND gate preserves the full approximation certificate: polynomial,
small Boolean error circuit, and pointwise norm bound. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def CircuitCertificate.andGate {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n)
    (H : ∀ i, CircuitCertificate ν s (c i)) :
    CircuitCertificate ν s (.andGate c) := by
  let P := fun i => (H i).polynomial
  let E := fun i => (H i).error
  let hs := exists_certified_and_sample ν s c E P
    (fun i => ((c i).size : ℝ) * (7 / 8 : ℝ) ^ s)
    (fun i => (H i).error_probability) (fun i => (H i).exact_off_error)
  let sample := Classical.choose hs
  have hprob := (Classical.choose_spec hs).1
  have hexact := (Classical.choose_spec hs).2
  refine
    { polynomial := fun x => sampledAndPolynomial sample (fun i => P i x)
      error := AC0Circuit.combineGateException sample c E
      degree_bound := ?_
      error_depth := ?_
      error_size := ?_
      error_probability := ?_
      exact_off_error := hexact
      norm_bound := ?_ }
  · exact sampledAndPolynomial_degree sample P _ (fun i =>
      ((H i).degree_bound).mono
        (le_sup (f := fun j => (c j).approximationDegree s) (mem_univ i)))
  · let D := univ.sup (fun i => (c i).depth)
    have hc (i : Fin k) : (c i).depth ≤ D :=
      le_sup (f := fun j => (c j).depth) (mem_univ i)
    have hE (i : Fin k) : (E i).depth ≤ 4 * D + 4 := by
      have hh := (H i).error_depth
      have hd := hc i
      dsimp only [E]
      omega
    have hh := AC0Circuit.combineGateException_depth sample c E hc hE (by omega)
    change (AC0Circuit.combineGateException sample c E).depth ≤ 4 * (1 + D) + 1
    omega
  · rw [AC0Circuit.combineGateException_size]
    have hs := AC0Circuit.gateSamplingException_size sample c
    have he : ∑ i, (E i).size ≤ ∑ i, (c i).exceptionSizeBound s :=
      sum_le_sum (fun i _ => (H i).error_size)
    change 1 + (AC0Circuit.gateSamplingException sample c).size + ∑ i, (E i).size ≤
      4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s
    omega
  · convert hprob using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]
  · intro x
    let B := ∑ i, (c i).sampleNormBound s
    have hB : 0 ≤ B := sum_nonneg (fun i _ => AC0Circuit.sampleNormBound_nonneg s (c i))
    have hP (i : Fin k) : |P i x| ≤ B :=
      ((H i).norm_bound x).trans
        (single_le_sum (fun j _ => AC0Circuit.sampleNormBound_nonneg s (c j)) (mem_univ i))
    have hb := sampledAndPolynomial_abs_le sample (fun i => P i x) hB hP
    have hp : (1 + (k : ℝ) * (1 + B)) ^ (s * (Nat.log 2 k + 3)) ≤
        (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3)) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    change |sampledAndPolynomial sample (fun i => P i x)| ≤
      1 + (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3))
    linarith

end TwoPointCorrelations

end OAI
