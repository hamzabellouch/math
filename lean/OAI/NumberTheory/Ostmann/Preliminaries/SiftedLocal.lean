import OAI.NumberTheory.Ostmann.Preliminaries.SiftedResidues
import OAI.NumberTheory.Ostmann.Supply.CRTPrimitiveEnergy
import OAI.NumberTheory.Ostmann.Supply.ResidueTensor

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

theorem local_product_le_primitive_energy {q : ℕ} [NeZero q] (hq : Squarefree q)
    (U : Finset ℕ) (hU : U.Nonempty)
    [∀ p : q.primeFactors, NeZero (p : ℕ)]
    (S : ∀ p : q.primeFactors, Finset (ZMod (p : ℕ)))
    (hSn : ∀ p, (S p).Nonempty)
    (hS : ∀ a ∈ U, ∀ p, (a : ZMod (p : ℕ)) ∈ S p) :
    (∏ p : q.primeFactors, Supply.complementRatio (S p)) ≤
      ∑ u : (ZMod q)ˣ, ‖normalizedExpSum U (((u : ZMod q).val : ℝ)/q)‖^2 := by
  classical
  have ht := Supply.residueTensorKernel_lower (fun p : q.primeFactors => (p : ℕ)) U S hSn hS
  have he := Supply.normalizedExpSum_primitive_energy_complex hq U
  have hcard : (U.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hU).ne'
  have hcardc : (U.card : ℂ)^2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hcard
  have he' := congrArg Complex.re ((eq_div_iff hcardc).mp he)
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re] at he'
  simp only [Complex.ofReal_natCast] at he'
  have hkernel :
      (∑ a ∈ U, ∑ b ∈ U, ∏ p : q.primeFactors,
        (((p : ℕ) : ℂ)*(if (a : ZMod (p : ℕ))=(b : ZMod (p : ℕ)) then 1 else 0)-1)) =
      (∑ a ∈ U, ∑ b ∈ U, ∏ p ∈ q.primeFactors,
        ((p : ℂ)*(if (a : ZMod p)=(b : ZMod p) then 1 else 0)-1)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact Finset.prod_coe_sort q.primeFactors
      (fun p : ℕ => (p : ℂ)*(if (a : ZMod p)=(b : ZMod p) then 1 else 0)-1)
  rw [hkernel, ← he'] at ht
  exact (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hcard)).mp (by simpa only [mul_comm] using ht)

end Ostmann.SiftedWeights

end OAI
