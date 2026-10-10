import Mathlib.NumberTheory.Divisors
import OAI.NumberTheory.Ostmann.Arithmetic.LcmFrequencySum

namespace OAI

/-! # Multiplicity of the reduced frequency modulus -/

namespace Ostmann

open scoped BigOperators

def reducedFrequency (g s : ℕ) : ℕ := s / s.gcd g

theorem reducedFrequency_mul_gcd (g s : ℕ) : reducedFrequency g s * s.gcd g = s :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left s g)

theorem reducedFrequency_mem {N g s : ℕ} (hs : s ∈ Finset.Icc 1 N) :
    reducedFrequency g s ∈ Finset.Icc 1 N := by
  obtain ⟨hs₀, hsN⟩ := Finset.mem_Icc.mp hs
  have hg := Nat.gcd_pos_of_pos_left g (show 0 < s from hs₀)
  exact Finset.mem_Icc.mpr ⟨Nat.div_pos
    (Nat.le_of_dvd hs₀ (Nat.gcd_dvd_left s g)) hg, (Nat.div_le_self _ _).trans hsN⟩

/-- A fixed reduced modulus has at most one frequency for each divisor
of the gcd of the two child frequencies. -/
theorem reducedFrequency_fiber_card_le (N g a : ℕ) (hg : g ≠ 0) :
    ((Finset.Icc 1 N).filter fun s => reducedFrequency g s = a).card ≤ g.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun s => s.gcd g)
  · intro s _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right s g, hg⟩
  · intro s hs t ht heq
    change s.gcd g = t.gcd g at heq
    have hsa := (Finset.mem_filter.mp hs).2
    have hta := (Finset.mem_filter.mp ht).2
    calc
      s = reducedFrequency g s * s.gcd g := (reducedFrequency_mul_gcd g s).symm
      _ = reducedFrequency g t * t.gcd g := by rw [hsa, hta, heq]
      _ = t := reducedFrequency_mul_gcd g t

theorem sum_reducedFrequency_le (N g : ℕ) (hg : g ≠ 0)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ Finset.Icc 1 N, F (reducedFrequency g s)) ≤
      g.divisors.card * ∑ a ∈ Finset.Icc 1 N, F a := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => reducedFrequency_mem (g := g) hs)
    (fun s => F (reducedFrequency g s))]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (g.divisors.card : ℝ) * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a),
          F (reducedFrequency g s)) =
          (((Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast reducedFrequency_fiber_card_le N g a hg)
        (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- After fixing the child frequencies, summing the two parent reduced
moduli costs only the divisor multiplicities and a cubic logarithm. -/
theorem reducedFrequency_lcm_sum_le (N g h : ℕ) (hg : g ≠ 0) (hh : h ≠ 0) :
    (∑ s ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
      (((reducedFrequency g s).lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹) ≤
      (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3 := by
  have hfirst := sum_reducedFrequency_le N g hg
    (fun a => ∑ t ∈ Finset.Icc 1 N, ((a.lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  calc
    _ ≤ (g.divisors.card : ℝ) *
        ∑ a ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          ((a.lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹ := hfirst
    _ ≤ (g.divisors.card : ℝ) *
        ∑ a ∈ Finset.Icc 1 N, (h.divisors.card : ℝ) *
          ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      exact sum_reducedFrequency_le N h hh
        (fun b => ((a.lcm b : ℕ) : ℝ)⁻¹) (fun _ _ => by positivity)
    _ = (g.divisors.card : ℝ) * h.divisors.card *
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_lcm_sum_le_log_cube N)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Ostmann

end OAI
