import OAI.Probability.ThorpShuffle.BlockFibers

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp
open scoped Classical

theorem law_realPower (d t k : ℕ) :
    law d (k*t) = Fourier.realPower (law d t) k := by
  induction k with
  | zero =>
      funext g
      simp only [Nat.zero_mul, law, run, List.ofFn_zero, List.reverse_nil, List.prod_nil,
        fairMass, Fourier.realPower]
      by_cases hg : g = 1
      · subst g
        simp
      · simp [hg, Ne.symm hg]
  | succ k ih =>
      rw [Nat.succ_mul, law_add, ih]
      rfl

namespace Specht
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

theorem trimmed_eight_tv (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (μ : Equiv.Perm α → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1)
    (hb : ∑ g, (μ g : ℂ) * complexSign g = 0)
    (hδ : Trim.discarded ψ μ ≤ 1/2) :
    tv (realPower μ 8) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) ≤
      8 * Trim.discarded ψ μ + (1/2 : ℝ) * Real.sqrt
        (2 * (2 * Trim.discarded ψ μ)^16 +
          (32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α)) := by
  let ν := Trim.normalized ψ μ
  have hd : Trim.discarded ψ μ < 1 := by linarith
  have hν : ∀ g, 0 ≤ ν g := Trim.normalized_nonneg ψ μ hμ hd
  have hν1 : ∑ g, ν g = 1 := Trim.normalized_sum ψ μ h1 hd
  have hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      4 * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
    intro i g
    convert Trim.normalized_coset ψ μ hμ hδ i g using 1
    apply Finset.sum_congr rfl
    intro h _
    congr 4
    exact Subsingleton.elim _ _
  have hpar := Trim.normalized_bias ψ μ hμ h1 hd complexSign
    (fun g => (complexSign_norm g).le) hb
  have hfour := permutation_eight_bound hn ψ ν 4 hν hν1 (by norm_num) hcoset
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hpar 16
  have hsq : (∑ g, |realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹|)^2 ≤
      2 * (2 * Trim.discarded ψ μ)^16 +
        (32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α) := by
    norm_num only [show (8:ℝ)*4 = 32 by norm_num] at hfour
    exact hfour.trans (by gcongr)
  have hnorm := Real.le_sqrt_of_sq_le hsq
  calc
    _ ≤ tv (realPower μ 8) (realPower ν 8) +
        tv (realPower ν 8) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) := tv_triangle _ _ _
    _ ≤ 8 * Trim.discarded ψ μ + _ := add_le_add
      (by simpa only [ν, Nat.cast_ofNat, Trim.normalized_tv ψ μ hμ h1 hd] using tv_realPower μ ν hμ h1 hν hν1 8)
      (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ) ≤ 1/2))

end Specht
end Thorp

end

end OAI
