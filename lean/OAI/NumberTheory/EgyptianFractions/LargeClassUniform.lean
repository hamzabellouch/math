import OAI.NumberTheory.EgyptianFractions.LargePrefixHarmonic
import OAI.NumberTheory.EgyptianFractions.DivisorClasses

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

attribute [local instance] Classical.propDecidable

/-- The canonical sorted-prefix large class satisfies the hypotheses of the
weighted large-prefix estimate. -/
theorem DivisorClasses.LargeClass.inLargePrefixClass {n : ℕ} {v Y : ℝ}
    (h : DivisorClasses.LargeClass n v Y) :
    InLargePrefixClass (Real.sqrt Y) (v ^ (15 / 16 : ℝ)) n := by
  rcases h with hsmall | ⟨d, p, hpref, hp⟩
  · exact Or.inl hsmall
  · obtain ⟨hd0, hprime, hd, hdY, hcross, hpd, hsmooth, hrough⟩ := hpref
    exact Or.inr ⟨d, p, hd, hdY, hprime, hp, hrough⟩

/-- Normalizing the size of the translated integer costs only one extra S
in its logarithmic bound. -/
theorem shifted_log_le_enlarged_scale (D S X Y : ℝ) (N h : ℕ)
    (hSlog : Real.log 2 ≤ S) (hX : 0 < X)
    (hhi : Real.log X ≤ D * S) (hN : (N : ℝ) ≤ Real.exp (D * S))
    (hh : 1 ≤ h) (hhY : (h : ℝ) ≤ Y) (hYX : Y ≤ X) :
    Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
  have hXS : X ≤ Real.exp (D * S) := by
    have he := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log hX] using he
  have htwo : (2 : ℝ) ≤ Real.exp S := by
    have he := Real.exp_le_exp.mpr hSlog
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hnpos : 0 < N + h := by omega
  have hnle : ((N + h : ℕ) : ℝ) ≤ Real.exp ((D + 1) * S) := by
    have hhle : (h : ℝ) ≤ Real.exp (D * S) := hhY.trans (hYX.trans hXS)
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hl := Real.log_le_log (by exact_mod_cast hnpos) hnle
  simpa only [Real.log_exp] using hl

/-- The complete eventual large-class estimate in the uniform moment range.
All prefix, harmonic, and translated-size hypotheses are discharged; only the
manuscript's size window remains. -/
theorem eventually_large_class_moment_bound (D r : ℝ) (_hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X → Real.log X ≤ D * S →
      Real.sqrt X ≤ Y → Y ≤ X → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.LargeClass (N + h) (Real.log X) Y),
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (((D + 1) * S) / Real.log X)) *
        (Real.log X) ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  classical
  obtain ⟨C, hC, hbound⟩ := large_prefix_class_sqrt_harmonic_bound r hr
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 32),
    eventually_ge_atTop (Real.log 2)] with S hSe hSlog
  intro X Y N hlo hhi hXY hYX hN
  have hSpos : 0 < S := (Real.exp_pos 32).trans_le hSe
  have hlog32 : 32 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).2 hSe
  have hlogpos : 0 < 2 * Real.log S := by linarith
  have hquad := Real.pow_div_factorial_le_exp (Real.log S) (by linarith) 2
  norm_num at hquad
  rw [Real.exp_log hSpos] at hquad
  have hlarge : 16 * Real.log S ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr hlog32) (show 0 ≤ Real.log S by linarith)
    nlinarith
  have hratio : 8 ≤ S / (2 * Real.log S) := (le_div_iff₀ hlogpos).2 (by linarith)
  have hlogX : 8 ≤ Real.log X := hratio.trans hlo
  have hX0 : 0 ≤ X := (Real.sqrt_nonneg X).trans (hXY.trans hYX)
  have hX1 : 1 < X := by
    by_contra hx
    have := Real.log_nonpos hX0 (le_of_not_gt hx)
    linarith
  have hXpos : 0 < X := by linarith
  have hXbig : 16 ≤ X := by
    have hexp : Real.exp 8 ≤ X := by
      simpa only [Real.exp_log hXpos] using Real.exp_le_exp.mpr hlogX
    have he := Real.pow_div_factorial_le_exp (8 : ℝ) (by norm_num) 2
    norm_num at he
    linarith
  have hY : 4 ≤ Y := by
    have hsqrt : 4 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0).2 (by norm_num; exact hXbig)
    exact hsqrt.trans hXY
  apply hbound X ((D + 1) * S) Y N
    ((Finset.Icc 1 ⌊Y⌋₊).filter
      (fun h => DivisorClasses.LargeClass (N + h) (Real.log X) Y))
    hX1 (by nlinarith) hY
  · exact Finset.filter_subset _ _
  · intro h hh
    obtain ⟨hhI, _⟩ := Finset.mem_filter.mp hh
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp hhI
    have hhYR : (h : ℝ) ≤ Y :=
      (by exact_mod_cast hhY : (h : ℝ) ≤ (⌊Y⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
    exact shifted_log_le_enlarged_scale D S X Y N h hSlog hXpos hhi hN hh1 hhYR hYX
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.inLargePrefixClass

/-- Exponential-cutoff form of the same complete class budget. -/
theorem eventually_large_class_moment_bound_exp (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.LargeClass (N + h) v Y),
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (((D + 1) * S) / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  obtain ⟨C, hC, hbound⟩ := eventually_large_class_moment_bound D r hD hr
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with S hS
  intro v Y N hlo hhi hXY hYX hN
  have hsqrt : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  simpa only [Real.log_exp] using hS (Real.exp v) Y N
    (by simpa only [Real.log_exp] using hlo)
    (by simpa only [Real.log_exp] using hhi)
    (by simpa only [hsqrt] using hXY) hYX hN

end Problem337

end

end OAI
