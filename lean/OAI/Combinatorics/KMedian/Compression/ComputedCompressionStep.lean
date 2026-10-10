import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedAffineKernel
import OAI.Combinatorics.KMedian.Compression.ComputedElimination

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressionStep {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (hsize : d+1 < μ.support.card) :
    IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2.1

theorem compressionStep_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    let ν := compressionStep μ v L hv hsize
    ν.denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) ∧
      ν.support ⊆ μ.support ∧ ν.support.card < μ.support.card ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  have he := eliminateAt_preserves μ (fun i j => (v i j:ℚ)) z p hp.1 hp.2
    hz.2.1 hz.2.2.1 hz.2.2.2.1
  change (eliminateAt μ z p hp.1 hp.2 hz.2.1).denominator ≤ _ ∧ _
  refine ⟨?_,he.2.2.2.1.trans (erase_subset _ _),?_,he.2.2.2.2⟩
  · change μ.denominator*z p ≤ _
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hz.2.2.2.2 p)) μ.denominator_pos.le
  · change (eliminateAt μ z p hp.1 hp.2 hz.2.1).support.card < μ.support.card
    have hh := card_le_card he.2.2.2.1
    rw [card_erase_of_mem ((μ.mem_support p).mpr he.2.1)] at hh
    omega

end MetricKMedian.IntegerLaw

end OAI
