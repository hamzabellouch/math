import OAI.MeasureTheory.Falconer.Estimates.BadTriplePower

namespace OAI

/-! # Power-small nearly dependent triples of retained original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem endpoint_bad_triples (H : ℕ) (hH : 0 < H) {ell a b e : ℝ}
    (hb : 0 < b) (hell : (h:ℝ) < ell)
    (hscale : 1/(H:ℝ) < a-2*b)
    (hgap : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ]
      (G : Set (Space n × Space n))
      (E : Set (Space n × Space n × Space n)), MeasurableSet E →
      (∀ w ∈ E, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
        ((2:ℝ)^N)^(-b) ≤ ‖w.2.1-w.1‖ ∧ ((2:ℝ)^N)^(-b) ≤ ‖w.2.2-w.1‖ ∧
        (w.1,w.2.2) ∈ G ∧
        Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
          (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1))) <
            2*((2:ℝ)^N)^(-a)) →
      (∀ p z, (p,z) ∈ G → z ≠ p) →
      (∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space n, ‖u‖ = 1 →
        μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell)) →
      (∫⁻ A : Fin h → Space (n+1),
        ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)))) E ∂gaussianRows (n+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := bad_triple_power_budget h H hH hb hell hscale hgap
  refine ⟨c,hc,N₀,?_⟩
  intro N hN μ _ G E hE hretained hdiag hcap
  obtain ⟨hscaleN,hbudget⟩ := hN₀ N hN
  have hpow : 0 < ((2:ℝ)^N)^(-b) := by positivity
  have hpow1 : ((2:ℝ)^N)^(-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  have heq : N/H+(N-N/H) = N := Nat.add_sub_of_le (Nat.div_le_self N H)
  have hh := gaussian_bad_triple_mass (h := h) (K := ((2:ℝ)^N)^e) μ G E hE hpow hpow1 (by positivity) hell
    (N/H) (N-N/H) hscaleN hretained hdiag (by simpa only [heq] using hcap)
  simp only [heq,measure_univ,one_pow,mul_one] at hh
  exact hh.trans hbudget

end Falconer

end OAI
