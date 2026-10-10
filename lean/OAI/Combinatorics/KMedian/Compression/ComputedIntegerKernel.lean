import Mathlib
import OAI.Combinatorics.KMedian.Compression.CircuitBitBound
import OAI.Combinatorics.KMedian.Compression.RationalScaling
import OAI.Combinatorics.KMedian.Compression.GaussianTabulated

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def computedIntegerKernel (r n : ℕ) (V : Fin r → Fin n → ℤ) : Fin n → ℤ :=
  let A := tabulate (fun i j => (V i j:ℚ))
  let q := kernelVector r n A
  let b := Vector.ofFn (RationalScaling.numerator (fun j => q[j.val]))
  fun j => b[j.val]

theorem computedIntegerKernel_spec (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    (∃ j, computedIntegerKernel r n V j ≠ 0) ∧
      (∀ i, ∑ j, computedIntegerKernel r n V j*V i j=0) ∧
      ∀ j, |computedIntegerKernel r n V j| ≤ (2:ℤ)^((2*r*(r+L))*(n+1)) := by
  let q := kernel r n (fun i j => (V i j:ℚ))
  have he : computedIntegerKernel r n V=RationalScaling.numerator q := by
    funext j
    dsimp only [computedIntegerKernel]
    simp only [Vector.getElem_ofFn,kernelVector_eq,values_tabulate]
    rfl
  rw [he]
  have hq := kernel_spec r n (fun i j => (V i j:ℚ)) hn
  have hb := integer_input_kernel_bounds r n L V hn hV
  let D := RationalScaling.denominator q
  have hD : (D:ℚ) ≠ 0 := by exact_mod_cast (RationalScaling.denominator_pos q).ne'
  have heq : ∀ j, (RationalScaling.numerator q j:ℚ)=q j*(D:ℚ) :=
    RationalScaling.numerator_cast q
  refine ⟨?_,?_,?_⟩
  · obtain ⟨j,hj⟩ := hq.1
    refine ⟨j,?_⟩
    intro hz
    have hh := heq j
    rw [hz,Int.cast_zero] at hh
    exact (mul_ne_zero hj hD) hh.symm
  · intro i
    have hi : (∑ j, (RationalScaling.numerator q j:ℚ)*(V i j:ℚ))=0 := by
      simp only [heq]
      calc
        _ = (∑ j, (V i j:ℚ)*q j)*(D:ℚ) := by
          rw [sum_mul]; apply sum_congr rfl; intro j _; ring
        _ = 0 := by rw [hq.2 i,zero_mul]
    exact_mod_cast hi
  · intro j
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound q (2*r*(r+L))
      (fun j => (hb j).1) (fun j => (hb j).2) j

end MetricKMedian.Gaussian

end OAI
