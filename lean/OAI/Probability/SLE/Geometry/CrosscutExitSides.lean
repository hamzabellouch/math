import OAI.Probability.SLE.Geometry.FirstDomainExit
import OAI.Probability.SLE.Geometry.PublishedCrosscutStraightening
import OAI.Probability.SLE.Geometry.PublishedConformalExitLaw

namespace OAI

/-! A nonzero real map-out limit has the sign selected before the first
domain exit. This turns geometric guide avoidance into an actual exit-arc
event, once the published conformal Brownian exit law is supplied. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.CrosscutSides
open RibbonCoordinates Target

theorem real_exit_positive_of_straightened_prefix
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (g : ℝ → ℂ) {a τ x : ℝ} (haτ : a < τ) (hx : x ≠ 0)
    (hprefix : ∀ t ∈ Ico a τ, 0 < (h (g t)).re)
    (hlim : Tendsto g (𝓝[<] τ) (𝓝 (x : ℂ))) : 0 < x := by
  have hh := straightening_preserves_real_exit_limit h hreal g x hlim
  have he : ∀ᶠ t in 𝓝[<] τ, 0 ≤ (h (g t)).re := by
    filter_upwards [Ioo_mem_nhdsLT haτ] with t ht
    exact (hprefix t ⟨ht.1.le, ht.2⟩).le
  exact lt_of_le_of_ne (ge_of_tendsto hh he) (Ne.symm hx)

theorem real_exit_negative_of_straightened_prefix
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (g : ℝ → ℂ) {a τ x : ℝ} (haτ : a < τ) (hx : x ≠ 0)
    (hprefix : ∀ t ∈ Ico a τ, (h (g t)).re < 0)
    (hlim : Tendsto g (𝓝[<] τ) (𝓝 (x : ℂ))) : x < 0 := by
  have hh := straightening_preserves_real_exit_limit h hreal g x hlim
  have he : ∀ᶠ t in 𝓝[<] τ, (h (g t)).re ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT haτ] with t ht
    exact (hprefix t ⟨ht.1.le, ht.2⟩).le
  exact lt_of_le_of_ne (le_of_tendsto hh he) hx

/-- The scalar straightened side coordinate has a fixed sign until exit
because its zero set is precisely the complete guide. -/
theorem positive_first_exit_belongs_to_arc
    (D : Set ℂ) (g : ℂ → ℂ) (h : ℂ ≃ₜ ℂ)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hg : ContinuousOn g D) (ζ : ℝ → ℂ) (hc : Continuous ζ)
    {τ : ℝ} (hτ : UnitWindowFirstExit D ζ τ)
    (haτ : (1 / 4 : ℝ) < τ)
    (hn : ∀ t ∈ Ico (1 / 4 : ℝ) τ, (h (g (ζ t))).re ≠ 0)
    (hstart : 0 < (h (g (ζ (1 / 4)))).re)
    (x : ℝ) (hx : x ≠ 0)
    (hlim : Tendsto (fun t => g (ζ t)) (𝓝[<] τ) (𝓝 (x : ℂ))) : 0 < x := by
  have hj : ContinuousOn (fun z => (h (g z)).re) D :=
    Complex.continuous_re.comp_continuousOn (h.continuous.comp_continuousOn hg)
  have hin : MapsTo ζ (Ico (1 / 4 : ℝ) τ) D :=
    hτ.2.2.mono_left (Ico_subset_Ico_left (by norm_num))
  exact real_exit_positive_of_straightened_prefix h hreal (fun t => g (ζ t)) haτ hx
    (exit_prefix_positive (fun z => (h (g z)).re) hj ζ hc.continuousOn hin hn haτ hstart)
    hlim

theorem negative_first_exit_belongs_to_arc
    (D : Set ℂ) (g : ℂ → ℂ) (h : ℂ ≃ₜ ℂ)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hg : ContinuousOn g D) (ζ : ℝ → ℂ) (hc : Continuous ζ)
    {τ : ℝ} (hτ : UnitWindowFirstExit D ζ τ)
    (haτ : (1 / 4 : ℝ) < τ)
    (hn : ∀ t ∈ Ico (1 / 4 : ℝ) τ, (h (g (ζ t))).re ≠ 0)
    (hstart : (h (g (ζ (1 / 4)))).re < 0)
    (x : ℝ) (hx : x ≠ 0)
    (hlim : Tendsto (fun t => g (ζ t)) (𝓝[<] τ) (𝓝 (x : ℂ))) : x < 0 := by
  have hj : ContinuousOn (fun z => (h (g z)).re) D :=
    Complex.continuous_re.comp_continuousOn (h.continuous.comp_continuousOn hg)
  have hin : MapsTo ζ (Ico (1 / 4 : ℝ) τ) D :=
    hτ.2.2.mono_left (Ico_subset_Ico_left (by norm_num))
  exact real_exit_negative_of_straightened_prefix h hreal (fun t => g (ζ t)) haτ hx
    (exit_prefix_negative (fun z => (h (g z)).re) hj ζ hc.continuousOn hin hn haτ hstart)
    hlim

end SLEExactGauge.CrosscutSides

end

end OAI
