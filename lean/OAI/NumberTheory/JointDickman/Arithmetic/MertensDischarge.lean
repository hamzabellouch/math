import OAI.NumberTheory.JointDickman.Amplification.ArithmeticInputs
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

namespace OAI

/-!
# Classical Mertens estimates

The reciprocal-prime sum and prime-product estimates use the same indexing
convention: the intervals `(0, floor x]` and `[2, floor x]` contain the same
primes.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_filter_Icc_eq_Ioc (N : ℕ) :
    (Icc 2 N).filter Nat.Prime = (Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [mem_filter,mem_Icc,mem_Ioc]
  constructor
  · rintro ⟨⟨hp,hN⟩,hprime⟩
    exact ⟨⟨by omega,hN⟩,hprime⟩
  · rintro ⟨⟨_,hN⟩,hprime⟩
    exact ⟨⟨hprime.two_le,hN⟩,hprime⟩

theorem primeReciprocalMertensInput : PublishedInputs.PrimeReciprocalMertensInput := by
  refine ⟨Erdos970.Mertens.M,Real.log 4 + 6 + Erdos970.Mertens.E₁,?_,?_⟩
  · have hE := Erdos970.Mertens.E₁.nonneg
    positivity
  · intro x hx
    rw [prime_filter_Icc_eq_Ioc]
    exact Erdos970.Mertens.E₂p.abs_le hx

theorem primeProductMertensInput : PublishedInputs.PrimeProductMertensInput := by
  have hE : Tendsto Erdos970.Mertens.E₃ atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Erdos970.Mertens.E₃.bound'
  have hlim : Tendsto (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Erdos970.Mertens.E₃ x)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * Real.exp 0)) :=
    tendsto_const_nhds.mul (Real.continuous_exp.tendsto 0 |>.comp hE)
  simp only [Real.exp_zero,mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_filter_Icc_eq_Ioc,
    Erdos970.Mertens.prod_one_minus_div_prime_eq (by linarith : 1 < x)]
  have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1 < x)).ne'
  field_simp

end JointDickman

end OAI
