import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTotientKernel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveMonotone

namespace OAI

/-! # The main-term comparison in Heath-Brown's quadratic-sieve recursion -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_totient_kernel_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H N D : ℕ, Squarefree D → Odd D → ∀ T : ℝ, 0 ≤ T →
      QuadraticSieveBound H N T → ∀ b : ℕ → ℂ, ∀ s : ℕ,
      (∑ r ∈ oddSquarefreeRange H,
        ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) ≤
        C * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_coprime_bilinear_epsilon ε hε
  refine ⟨C, hC, ?_⟩
  intro H N D hD hDo T hT h b s
  have hr : (∑ r ∈ oddSquarefreeRange H,
      ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) =
      ∑ r ∈ oddSquarefreeRange H,
        ‖quadraticGcdKernelSum (N / D) 1 (quadraticTotientCoeff D s b) r‖ := by
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      quadratic_totient_kernel_reduction hD hDo b s (r : ℤ)
  rw [hr]
  apply (hc H (N / D) T hT (h.mono_second (Nat.div_le_self N D)) _).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C * T)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self N D) hε.le
  · exact quadraticTotientCoeff_energy_le hD hDo s b
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · positivity

noncomputable def quadraticMainDifference (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) *
    (quadraticTotientKernelSum N D b w / (Real.sqrt (w : ℝ) : ℂ))

/-- The actual arithmetic main-term difference is controlled by quadratic
energy at the shorter frequency range. All divisor losses are explicit. -/
theorem quadratic_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D K : ℕ, Squarefree D → Odd D → 0 < K →
      ∀ T : ℝ, 0 ≤ T → QuadraticSieveBound (K * D ^ 2) N T → ∀ b : ℕ → ℂ,
      ‖quadraticMainDifference N D K b‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt (K : ℝ) * T * quadraticSieveEnergy N b := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadraticMainGamma_weighted_sum_bound ε hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_totient_kernel_sum_bound ε hε
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_divisor_bound ε hε
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro N D K hD hDo hK T hT h b
  have hs : (∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2),
      ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) ≤
      (D.divisors.card : ℝ) * (C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b) := by
    calc
      _ ≤ ∑ _s ∈ D.divisors,
          C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b :=
        Finset.sum_le_sum (fun s _ => hc₂ _ _ _ hD hDo T hT h b s)
      _ = _ := by simp
  have he : 0 ≤ quadraticSieveEnergy N b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs' := hs.trans (mul_le_mul_of_nonneg_right (hc₃ D hD.ne_zero)
    (by positivity : 0 ≤ C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b))
  have hw := hc₁ D K hD hDo hK (fun w => quadraticTotientKernelSum N D b w)
  have hh := hw.trans (mul_le_mul_of_nonneg_left hs'
    (by positivity : 0 ≤ C₁ * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ)))
  change ‖quadraticMainDifference N D K b‖ ≤ _ at hh
  convert hh using 1
  ring

end Ostmann

end OAI
