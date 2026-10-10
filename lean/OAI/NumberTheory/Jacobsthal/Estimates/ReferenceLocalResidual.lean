import OAI.NumberTheory.Jacobsthal.Harmonic.WeightedAnomalyConvergence
import OAI.NumberTheory.Jacobsthal.Sieve.ReferenceEulerRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceLocalResidual

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ReferenceAdmission ReferencePruning
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceMertens ReferenceDifferentiation
open ReferenceBenchmarkDecay ReferenceCancellation BoundaryAnomaly
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def nodeBenchmark (w : ℝ) (z : Node) : ℝ :=
  referenceProduct w z.cutoff z.closed*parentBenchmark z.side z.ratio

noncomputable def sourceResidual (w : ℝ) (z : Node) : ℝ :=
  referenceProduct w 2 true*(benchmark z.side (z.gap/2)-1)-
    referenceProduct w z.cutoff z.closed*(parentBenchmark z.side z.ratio-1)-
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def sourceInsertion (w : ℝ) (z : Node) : ℝ :=
  referencePolynomial w (boundaryPrimes w) z.side z.gap-nodeBenchmark w z-
    ∑ p ∈ highPrimes w z.cutoff z.closed,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*nodeBenchmark w (step w z p) else 0

theorem admitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : childAdmitted z.side z.gap (primeExponent w p)) :
    nodeBenchmark w (step w z p)=referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  unfold nodeBenchmark
  simp only [step]
  congr 1
  cases hi : z.side with
  | even => rfl
  | odd =>
    have hh : 2*primeExponent w p ≤ z.gap-primeExponent w p := by
      rw [hi] at ha
      exact (upper_admission_above_two hxp.le).mp ha
    have hc : 2 ≤ childRatio w z.gap p := by
      unfold childRatio
      have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ (by linarith)).mpr (by linarith)
      linarith
    exact parent_even_eq_ordinary hc

theorem omitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : ¬childAdmitted z.side z.gap (primeExponent w p)) :
    benchmark z.side.flip (childRatio w z.gap p)=0 := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  cases hi : z.side with
  | even => exact False.elim (ha (by rw [hi]; trivial))
  | odd =>
    have hh := actual_omitted_deviation_above_two hxp.le (by rwa [hi] at ha)
    change benchmark .even (z.gap/primeExponent w p-1)=0
    linarith

theorem admitted_benchmark_sum {w : ℝ} (hw : 1 < w) (z : Node) :
    (∑ p ∈ highPrimes w z.cutoff z.closed,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*nodeBenchmark w (step w z p) else 0)=
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ha : childAdmitted z.side z.gap (primeExponent w p)
  · rw [ite_eq_left ha,admitted_child_benchmark hw z hp ha]
    ring
  · rw [ite_eq_right ha,omitted_child_benchmark hw z hp ha,mul_zero]

theorem source_insertion_identity {w : ℝ} (hw : 1 < w) (z : Node) (hb : 2 < z.cutoff) :
    sourceInsertion w z=anomaly w z.side z.gap+sourceResidual w z := by
  have hp := actual_product_cutoff_identity hw hb z.closed
  have hsum : (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1))=
    (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p))-
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  unfold sourceInsertion sourceResidual anomaly
  rw [admitted_benchmark_sum hw z,hsum,hbase]
  unfold nodeBenchmark
  linarith

end NumberTheoryLean.ReferenceLocalResidual

end

end Erdos970

end OAI
