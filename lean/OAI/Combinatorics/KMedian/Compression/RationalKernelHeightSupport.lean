import Mathlib
import OAI.Combinatorics.KMedian.Compression.CircuitBitBound
import OAI.Combinatorics.KMedian.Compression.RationalScaling

namespace OAI


                                                   
section
namespace MetricKMedian.Gaussian
open Finset

theorem row_scaling_kernel_iff {r n : ℕ} (A : Fin r → Fin n → ℚ)
    (s : Fin r → ℚ) (hs : ∀ i, s i ≠ 0) (z : Fin n → ℚ) :
    (∀ i, ∑ j, (A i j*s i)*z j=0) ↔ (∀ i, ∑ j, A i j*z j=0) := by
  have he : ∀ i, (∑ j, (A i j*s i)*z j)=(∑ j, A i j*z j)*s i := by
    intro i
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    ring
  simp only [he,mul_eq_zero,hs,or_false]

theorem rational_input_kernel_bounds (r n L : ℕ) (A : Fin r → Fin n → ℚ)
    (hn : r < n) (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L) :
    let z := kernel r n A
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L*(n+1))) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L*(n+1))) := by
  dsimp only
  let V : Fin r → Fin n → ℤ := fun i => RationalScaling.numerator (A i)
  let D : Fin r → ℚ := fun i => RationalScaling.denominator (A i)
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    apply ne_of_gt
    dsimp only [D]
    exact_mod_cast RationalScaling.denominator_pos (A i)
  have hV : ∀ i j, (V i j:ℚ)=A i j*D i := fun i j =>
    RationalScaling.numerator_cast (A i) j
  have hVb : ∀ i j, |V i j| ≤ (2:ℤ)^(L*(n+1)) := by
    intro i j
    simpa only [Fintype.card_fin] using
      RationalScaling.numerator_bound (A i) L (hnum i) (hden i) j
  have hki : ∀ z : Fin n → ℚ,
      (∀ i, ∑ j, (V i j:ℚ)*z j=0) ↔ (∀ i, ∑ j, A i j*z j=0) := by
    intro z
    simp only [hV]
    exact row_scaling_kernel_iff A D hD z
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n A hn
  have hk := (kernel_spec r n A hn).2
  have hcV : IsCircuit (fun i j => (V i j:ℚ)) (kernel r n A) := by
    intro v hv hkV
    exact hc v hv ((hki v).mp hkV)
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ (L*(n+1)) hVb
    ((hki _).mpr hk) hcV w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian
end

end OAI
