import OAI.Probability.SLE.Gauge.DenseCoverAdaptedTests

namespace OAI

/-! Adapted tests need conditional estimates only inside the retained
scale window. The discarded early scales need no dense estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem cover_window_failure_bound_on_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (success : ℕ → Set Ω)
    (n : ℕ) (hn : 1 ≤ n)
    (hmeas : ∀ j ∈ coverTestWindow n, MeasurableSet[F (j + 1)] (success j))
    (hstep : ∀ j ∈ coverTestWindow n, ∀ B : Set Ω, MeasurableSet[F j] B →
      ENNReal.ofReal (1 / Real.sqrt (n : ℝ)) * μ B ≤ μ (B ∩ success j)) :
    μ (⋂ j ∈ coverTestWindow n, (success j)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  classical
  let S : ℕ → Set Ω := fun j => if j ∈ coverTestWindow n then success j else univ
  have hS (j : ℕ) : MeasurableSet[F (j + 1)] (S j) := by
    dsimp only [S]
    split_ifs with hj
    · exact hmeas j hj
    · exact MeasurableSet.univ
  have hp : ENNReal.ofReal (1 / Real.sqrt (n : ℝ)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 1 ≤ Real.sqrt (n : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnr
    exact (div_le_one (zero_lt_one.trans_le hs)).mpr hs
  have hstep' (j : ℕ) (B : Set Ω) (hB : MeasurableSet[F j] B) :
      ENNReal.ofReal (1 / Real.sqrt (n : ℝ)) * μ B ≤ μ (B ∩ S j) := by
    dsimp only [S]
    split_ifs with hj
    · exact hstep j hj B hB
    · simpa only [inter_univ, one_mul] using mul_le_mul' hp (le_refl (μ B))
  have he : (⋂ j ∈ coverTestWindow n, (S j)ᶜ) =
      ⋂ j ∈ coverTestWindow n, (success j)ᶜ := by
    apply iInter_congr
    intro j
    apply iInter_congr
    intro hj
    simp only [S, ite_eq_left hj]
  simpa only [he] using cover_window_failure_bound μ F S hS n hn hstep'

end SLEExactGauge

end

end OAI
