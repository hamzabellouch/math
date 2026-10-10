import OAI.MeasureTheory.Falconer.Measures.InactiveBinIntegral
import OAI.MeasureTheory.Falconer.Geometry.InactiveBinScales

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem inactive_bin_ratio_bound (N L : ℕ) {sig t u c Λ : ℝ}
    (hsig : 0 ≤ sig) (hc : 0 < c)
    (ht : t ≤ u+2*sig*(N : ℝ)) (hu : 10*sig*(N : ℝ) ≤ u)
    (hL : (L : ℝ) ≤ u+2*sig*(N : ℝ))
    (hΛ : c*(2 : ℝ)^(t+u) ≤ Λ) :
    max (sourceSymbolScale N sig L) (graphUncappedAngularScale N sig t)⁻¹ /
      (Λ*graphUncappedAngularScale N sig t) ≤ c⁻¹*((2 : ℝ)^N)^(-18*sig) := by
  obtain ⟨h1,h2⟩ := inactive_bin_scale_slack N L hsig hc ht hu hL hΛ
  have hδ := graphUncappedAngularScale_pos N sig t
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  rw [← max_div_div_right (mul_nonneg hΛp.le hδ.le)]
  apply max_le
  · exact h2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith))
      (inv_nonneg.mpr hc.le))
  · have hi := inv_anti₀ (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)) h1
    have he : (c*((2 : ℝ)^N)^(18*sig))⁻¹ = c⁻¹*((2 : ℝ)^N)^(-18*sig) := by
      rw [mul_inv_rev, show -18*sig = -(18*sig) by ring, Real.rpow_neg (by positivity)]
      ring
    rw [he] at hi
    simpa only [div_eq_mul_inv, mul_inv_rev, pow_two, mul_assoc] using hi

theorem inactive_bin_integral_power {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c) :
    ∃ n : ℕ, ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
    ∀ (e : UnitCircle) (φ : ℝ), |φ| ≤ Real.pi →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*(sourceSymbolScale N sig L)^k) →
    ((2 : ℝ)^N)^outer * ‖∫ x : ℝ, cosineOscillator Λ (x-φ) *
      (w x * selectedBinAmplitude (graphUncappedAngularScale N sig t)
        (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
          (3*graphUncappedAngularScale N sig t)) f x)‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+outer+1)/(18*sig))
  have hexp : outer+1+(-18*sig)*(n : ℝ) ≤ -T := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 18*sig)).mp hn
    nlinarith
  obtain ⟨A,hA,hbound⟩ := inactive_bin_integral_bound hw hab hsw n
  obtain ⟨Ncap,hcap⟩ := graphAngularScale_cap_inactive hgap (by norm_num : (0 : ℝ) < 1)
  refine ⟨n,?_⟩
  intro C hC
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (by norm_num : (0 : ℝ) < 1) (A*C*c⁻¹^n)
  refine ⟨max Ncap Nc,?_⟩
  intro N hN L t u Λ hlow ht hu hL hΛ e φ hφ hmove hcone f hf hb
  have hδ := graphUncappedAngularScale_pos N sig t
  have hδ1 : graphUncappedAngularScale N sig t ≤ 1 := by
    have he := hcap N ((le_max_left _ _).trans hN) t hlow
    have hm := min_le_left 1 (graphUncappedAngularScale N sig t)
    change min 1 (graphUncappedAngularScale N sig t) = graphUncappedAngularScale N sig t at he
    rwa [he] at hm
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  have hi := hbound _ hδ hδ1 e φ hφ hmove hcone hf hC (sourceSymbolScale_pos N sig L).le hΛp hb
  have hr := inactive_bin_ratio_bound N L hsig.le hc ht hu hL hΛ
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    max (sourceSymbolScale N sig L) (graphUncappedAngularScale N sig t)⁻¹ /
      (Λ*graphUncappedAngularScale N sig t)) hr n
  have hR : 1 ≤ (2 : ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2 : ℝ)^N := by positivity
  have hA' : A*C*c⁻¹^n ≤ (2 : ℝ)^N := by
    simpa only [Real.rpow_one] using hconst N ((le_max_right _ _).trans hN)
  calc
    _ ≤ ((2 : ℝ)^N)^outer * (A*C*(c⁻¹*((2 : ℝ)^N)^(-18*sig))^n) := by
      exact mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hA hC))) (by positivity)
    _ = (A*C*c⁻¹^n) * ((2 : ℝ)^N)^(outer+(-18*sig)*(n : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hRp.le, Real.rpow_add hRp]
      ring
    _ ≤ (2 : ℝ)^N * ((2 : ℝ)^N)^(outer+(-18*sig)*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hA' (by positivity)
    _ = ((2 : ℝ)^N)^(outer+1+(-18*sig)*(n : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one ((2 : ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR hexp

end PlanarFalconer

end OAI
