import OAI.Probability.SLE.Multipoint.MultipointActualPhases

namespace OAI

/-! A countable family of concrete localizations, with the original
radius stops capped beyond each integration horizon. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem exists_actual_localizations
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (u₀ u₂ : ι → ℝ) (h₀ : ∀ i, 0 ≤ u₀ i) (hu : ∀ i, u₀ i ≤ u₂ i)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (A : ℝ) (hA : 0 ≤ A) (hzA : ∀ i, |Real.log (z i).im| ≤ A) :
    Nonempty (∀ n : ℕ, LocalizedState B hm κ (-(A+n+1)) (A+n+1) (A+n+1)
      ((n : ℝ≥0)+1) z
      (fun i => actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2)) γ G) := by
  classical
  have hn (n : ℕ) : 0 ≤ A+(n : ℝ)+1 := by positivity
  have hex (n : ℕ) : Nonempty (LocalizedState B hm κ (-(A+n+1)) (A+n+1) (A+n+1)
      ((n : ℝ≥0)+1) z
      (fun i => actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2)) γ G) := by
    have ht := (actualFactorStops_regular hB hm hBm hBc hB0 κ hκ hκ8 γ G F hw
      z hz u₀ u₂ h₀ hu ((n : ℝ≥0)+1)).1
    apply exists_localizedState B hm hBm hBc κ (-(A+n+1)) (A+n+1) (A+n+1)
      (by linarith [hn n]) ((n : ℝ≥0)+1) z hz
    · intro i
      have hi := (abs_le.mp (hzA i)).1
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro i
      have hi := (abs_le.mp (hzA i)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro ω
      simpa only [hB0 ω,abs_zero] using hn n
    · exact fun i => ht (i,2)
    · exact hw
  exact ⟨fun n => Classical.choice (hex n)⟩

lemma initial_log_height_bound {ι : Type*} [Fintype ι] (z : ι → ℂ) (i : ι) :
    |Real.log (z i).im| ≤ ‖fun j => Real.log (z j).im‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j => Real.log (z j).im) i

end SLEExactGauge.Multipoint

end

end OAI
