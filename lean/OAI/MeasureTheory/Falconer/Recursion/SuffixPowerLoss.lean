import OAI.MeasureTheory.Falconer.Recursion.ActualSuffixReduction

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_coefficient_absorption {sig eps : ℝ}
    (hsig : 0 ≤ sig) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a lam : ℝ, 0 ≤ lam →
      2255*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) ≤
        ((2:ℝ)^N)^(a+4000*(lam+sig)+eps) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed heps 2255
  refine ⟨N₀,?_⟩
  intro N hN a lam hlam
  calc
    _ ≤ ((2:ℝ)^N)^eps*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(eps+(a+2000*(lam+sig)+12*lam)) := by
      rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem uniform_actual_suffix_reduction {sig eps : ℝ} (hsig : 0 < sig)
    (heps : 0 < eps) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q → 0 ≤ d.lam →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+4000*(d.lam+sig)+eps)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₁,h₁⟩ := uniform_suffix_reduction_explicit hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_suffix_coefficient_absorption hsig.le heps
  refine ⟨max N₁ N₂,?_⟩
  intro d hsig' hJ' hN hQ hs hq hlam hX hY B δ hprof hw htN hi A p hsuffix
  apply (h₁ d hsig' hJ' ((le_max_left _ _).trans hN) hQ hs hq hX hY B δ hprof hw htN hi hsuffix).trans
  apply mul_le_mul' _ le_rfl
  have hh := ENNReal.ofReal_le_ofReal (h₂ d.N ((le_max_right _ _).trans hN)
    (A p-intervalMin A p d.t) d.lam hlam)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2255),ENNReal.ofReal_ofNat] using hh

end PlanarFalconer

end OAI
