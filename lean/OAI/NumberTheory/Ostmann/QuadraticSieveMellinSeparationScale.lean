import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationGcd

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem mellinWeightedEnergy_le (S : Finset ℕ) (a : ℕ → ℂ) (β : ℕ → ℝ)
    (σ : ℝ) (hσ : 0 ≤ σ) (hβ : ∀ n ∈ S, 1 ≤ β n) :
    mellinWeightedEnergy S a β σ ≤ coefficientEnergy S a := by
  unfold mellinWeightedEnergy coefficientEnergy
  apply Finset.sum_le_sum
  intro n hn
  have h := Real.rpow_le_one_of_one_le_of_nonpos (hβ n hn) (neg_nonpos.mpr hσ)
  have h0 : 0 ≤ (β n) ^ (-σ) := Real.rpow_nonneg (by linarith [hβ n hn]) _
  have hs : ((β n) ^ (-σ)) ^ 2 ≤ 1 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_one _)

theorem mellinWeightedEnergy_sqrt_le (S : Finset ℕ) (a : ℕ → ℂ)
    (σ : ℝ) (hσ : 0 ≤ σ) (hS : ∀ n ∈ S, 0 < n) :
    mellinWeightedEnergy S a (fun n => Real.sqrt n) σ ≤ coefficientEnergy S a := by
  apply mellinWeightedEnergy_le S a _ σ hσ
  intro n hn
  exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n from hS n hn))

theorem mellin_outer_sqrt_scale_bound (c B σ : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hσ : 0 ≤ σ) (v : ℕ) (hv : 0 < v) (hvB : (v : ℝ) ≤ B) :
    (c / Real.sqrt v) ^ (-σ) ≤ (c / Real.sqrt B) ^ (-σ) := by
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  apply Real.rpow_le_rpow_of_nonpos (div_pos hc hsB) _ (neg_nonpos.mpr hσ)
  exact div_le_div_of_nonneg_left hc.le hsv (Real.sqrt_le_sqrt hvB)

theorem mellin_sqrt_scale_factorization (c : ℝ) (v n t : ℕ) :
    c / Real.sqrt v * Real.sqrt n * Real.sqrt t =
      c * Real.sqrt ((n : ℝ) * (t : ℝ)) / Real.sqrt v := by
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem coprime_jacobi_mellin_sqrt_gcd_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ) (c B : ℝ),
      d ≠ 0 → (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N → 0 < c → 0 < B →
      ∃ d₁ d₂ : ℕ, 0 < d₁ ∧ 0 < d₂ ∧ d₁ * d₂ = d ∧
        (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
          if n.Coprime t ∧ d ∣ n * t then a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) *
            ρ (c * Real.sqrt ((n : ℝ) * (t : ℝ)) / Real.sqrt v) else 0‖) ≤
          (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖) *
            (c / Real.sqrt B) ^ (-σ) *
            Real.sqrt (C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
              quadraticNorm V (oddSquarefreeUpTo (N / d₂)) *
              coefficientEnergy S a * coefficientEnergy T b) := by
  obtain ⟨C, hC, hmain⟩ := coprime_jacobi_mellin_gcd_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro ρ σ hσ V S T a b d N c B hd hV hS hT hc hB
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := (mem_oddSquarefreeUpTo.mp (hS hn)).1
  have hTpos (t : ℕ) (ht : t ∈ T) : 0 < t := (mem_oddSquarefreeUpTo.mp (hT ht)).1
  have hβ (n : ℕ) (hn : n ∈ S) : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hSpos n hn)
  have hγ (t : ℕ) (ht : t ∈ T) : 0 < Real.sqrt (t : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hTpos t ht)
  have hα (v : ℕ) (hv : v ∈ V) : 0 < c / Real.sqrt (v : ℝ) :=
    div_pos hc (Real.sqrt_pos.mpr (by exact_mod_cast (hV v hv).1))
  obtain ⟨d₁, d₂, hd₁, hd₂, hprod, hb⟩ := hmain ρ σ hσ V S T a b d N
    (fun v => c / Real.sqrt v) (fun n => Real.sqrt n) (fun t => Real.sqrt t)
    ((c / Real.sqrt B) ^ (-σ)) hd (fun v hv => (hV v hv).2.1) hS hT hα hβ hγ
    (Real.rpow_nonneg (by positivity) _)
    (fun v hv => mellin_outer_sqrt_scale_bound c B σ hc hB hσ.le v (hV v hv).1 (hV v hv).2.2)
  refine ⟨d₁, d₂, hd₁, hd₂, hprod, ?_⟩
  simp only [mellin_sqrt_scale_factorization] at hb
  apply hb.trans
  have hEA := mellinWeightedEnergy_sqrt_le S a σ hσ.le hSpos
  have hEB := mellinWeightedEnergy_sqrt_le T b σ hσ.le hTpos
  have hbase : 0 ≤ C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
      quadraticNorm V (oddSquarefreeUpTo (N / d₂)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (quadraticNorm_nonneg _ _)) (quadraticNorm_nonneg _ _)
  have hM : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hEA hbase) hEB
    (mellinWeightedEnergy_nonneg _ _ _ _)
    (mul_nonneg hbase (coefficientEnergy_nonneg _ _))

end Ostmann.QuadraticSieve

end OAI
