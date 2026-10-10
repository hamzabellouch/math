import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupSupport
import OAI.Probability.InvariantIsing.Magnetic.MagneticTrialLimit

namespace OAI

/-! Magnetic entropy identification from the proved scalar supporting
inequality, with no additional concavity premise. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_entropy_sequence {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1) (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n)+fieldPairing p (h n)/2)
      atTop (𝓝 (magneticEntropyFunctional γ mag p).toReal) :=
  magnetic_entropy_sequence_of_support γ mag hγ hγsum (fun a => (hmag a).le)
    p h hC (fun n k => magneticGroup_support γ mag hγ hγsum hmag (h n) k) hself

theorem magnetic_entropy_trial_tendsto {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n)+fieldPairing (q n) (h n)/2+
      spectralFunctional (finiteR ρ eig hρ hsum) (q n)) atTop
      (𝓝 ((magneticEntropyFunctional γ mag p).toReal+spectralFunctional (finiteR ρ eig hρ hsum) p)) :=
  magnetic_entropy_trial_tendsto_of_support ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).le) p q h hC
    (fun n k => magneticGroup_support γ mag hγ hγsum hmag (h n) k) hself hq

theorem magnetic_entropy_trial_eventually_lower {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal-ε ≤
        magneticGroupValue γ mag (h n)+fieldPairing (q n) (h n)/2+
          spectralFunctional (finiteR ρ eig hρ hsum) (q n) :=
  magnetic_entropy_trial_eventually_lower_of_support ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).le) p q h hC
    (fun n k => magneticGroup_support γ mag hγ hγsum hmag (h n) k) hself hq

end InvariantIsing

end

end OAI
