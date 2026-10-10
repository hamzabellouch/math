import OAI.Probability.SLE.Multipoint.MultipointCutoffSuccess

namespace OAI

/-! Integer localization bounds eventually contain every successful finite
family of completion prefixes. Height monotonicity reduces the spatial
bound to the two endpoints of each individual prefix. -/

noncomputable section
open Set Filter MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem completion_prefixes_bounded_by_nat
    {ι : Type*} [Fintype ι]
    (B : ℝ≥0 → ℝ) (hB : Continuous B)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F)
    (z : ι → ℂ) (τ : ι → ℝ≥0)
    (hlive : ∀ i, z i ∈ survivingDomain γ (τ i)) (T : ℝ≥0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ t : ℝ≥0, t ≤ T → |B t| < (n : ℝ)) ∧
      (∀ i (t : ℝ≥0), t ≤ τ i →
        (logLoewnerCoordinates G (z i) t).1.im ∈ Ioo (-(n : ℝ)) (n : ℝ)) := by
  classical
  obtain ⟨b,hb⟩ := continuous_path_bounded_by_nat B hB T
  let C : ℝ := ∑ i, (|Real.log (G (τ i) (z i)).im| + |Real.log (z i).im|)
  obtain ⟨k,hk⟩ := exists_nat_gt C
  refine ⟨max (b+1) k, fun n hn => ⟨?_, ?_⟩⟩
  · intro t ht
    have hbn : (b : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (le_max_left (b+1) k).trans hn
    exact (hb t ht).trans_le hbn
  · intro i t ht
    have hi : |Real.log (G (τ i) (z i)).im| + |Real.log (z i).im| ≤ C := by
      exact Finset.single_le_sum
        (f := fun j => |Real.log (G (τ j) (z j)).im| + |Real.log (z j).im|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right (b+1) k).trans hn
    have hh := hw.log_height_bounds (τ i) (z i) (hlive i) t
      (show (t : ℝ) ∈ Icc 0 (τ i : ℝ) from ⟨t.coe_nonneg, by exact_mod_cast ht⟩)
    simp only [Real.toNNReal_coe] at hh
    have hl := neg_abs_le (Real.log (G (τ i) (z i)).im)
    have hu := le_abs_self (Real.log (z i).im)
    have hla := abs_nonneg (Real.log (G (τ i) (z i)).im)
    have hua := abs_nonneg (Real.log (z i).im)
    have hresult : Real.log (G t (z i)).im ∈ Ioo (-(n : ℝ)) (n : ℝ) := by
      constructor <;> linarith
    simpa only [logLoewnerCoordinates, Real.toNNReal_coe, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hresult

/-- The standard integer localizations eventually survive beyond any
fixed successful completion horizon. Their frozen completion times may
be horizon truncations, provided those truncations eventually agree. -/
theorem eventually_localization_after_completed
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ A : ℝ) (hA : 0 ≤ A) (z : ι → ℂ)
    (τ : ℕ → ι → Ω → ℝ≥0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) (F ω))
    (S : ∀ n : ℕ, LocalizedState B hm κ (-(A+n+1)) (A+n+1) (A+n+1)
      ((n : ℝ≥0)+1) z (τ n) γ G)
    (ω : Ω) (σ : ι → ℝ≥0) (T : ℝ≥0)
    (hσ : ∀ i, σ i ≤ T)
    (hlive : ∀ i, z i ∈ survivingDomain (γ ω) (σ i))
    (hτ : ∀ᶠ n : ℕ in atTop, ∀ i, τ n i ω = σ i) :
    ∀ᶠ n : ℕ in atTop, T < (S n).χ ω := by
  obtain ⟨N,hN⟩ := completion_prefixes_bounded_by_nat
    (fun t => B t ω) (hBc ω) (hw ω) z σ hlive T
  have hlarge : ∀ᶠ n : ℕ in atTop, (T : ℝ) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (T : ℝ))
  filter_upwards [eventually_ge_atTop N, hlarge, hτ] with n hn hT hτn
  have hupper : (n : ℝ) ≤ A+n+1 := by linarith
  apply (S n).cutoff_after_completed ω T
  · exact_mod_cast (show (T : ℝ) < (n : ℝ)+1 from by linarith)
  · intro i
    rw [hτn i]
    exact hσ i
  · intro t ht
    exact ((hN n hn).1 t ht).trans_le hupper
  · intro i t ht
    rw [hτn i] at ht
    have hi := (hN n hn).2 i t ht
    exact ⟨(neg_le_neg hupper).trans_lt hi.1, hi.2.trans_le hupper⟩

end SLEExactGauge.Multipoint

end

end OAI
