import OAI.Probability.InvariantIsing.Magnetic.MagneticEntropySequence
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalBounds
import OAI.Probability.InvariantIsing.Fields.FieldPairingContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralPathLimit

namespace OAI

/-! Identification of the magnetic cavity trial from weighted
self-consistency and its supporting inequality. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_entropy_trial_tendsto_of_support {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s *
        (fieldFunction k s-fieldFunction (h n) s) ∂pathMeasure)/2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
      spectralFunctional (finiteR ρ eig hρ hsum) (q n)) atTop
      (𝓝 ((magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p)) := by
  obtain ⟨htop,hent⟩ := magnetic_entropy_sequence_of_support γ mag hγ hγsum hmag p h hC hsupport hself
  have hpair := field_pairing_path_tendsto p q h hC hq
  have hspec := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hsum p q hq zero_le_one
  simp only [finiteTemperatureFunctional_eq ρ eig hρ hsum _ zero_le_one,one_mul] at hspec
  refine ⟨htop,?_⟩
  have ht := (hent.add (hpair.div_const 2)).add hspec
  have he : (fun n => (magneticGroupValue γ mag (h n) + fieldPairing p (h n)/2 +
      (fieldPairing (q n) (h n)-fieldPairing p (h n))/2) +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) =
      (fun n => magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) := by
    funext n
    ring
  rw [he] at ht
  simpa only [zero_div,add_zero] using ht

theorem magnetic_entropy_trial_eventually_lower_of_support {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s *
        (fieldFunction k s-fieldFunction (h n) s) ∂pathMeasure)/2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal - ε ≤
        magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
          spectralFunctional (finiteR ρ eig hρ hsum) (q n) := by
  obtain ⟨htop,ht⟩ := magnetic_entropy_trial_tendsto_of_support
    ρ eig hρ hsum γ mag hγ hγsum hmag p q h hC hsupport hself hq
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ := ne_bot_of_le_ne_bot
    (EReal.coe_ne_bot _) (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
  have hfinite := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum hmag
  have hi := iInf_le (fun v : OverlapPath => magneticEntropyFunctional γ mag v +
    (spectralFunctional (finiteR ρ eig hρ hsum) v : EReal)) p
  change magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag ≤ _ at hi
  rw [← EReal.coe_toReal hfinite.1 hfinite.2, ← EReal.coe_toReal htop hbot,
    ← EReal.coe_add] at hi
  have hi' : (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal ≤
      (magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p := by
    exact_mod_cast hi
  intro ε hε
  have he := ht.eventually (lt_mem_nhds (show
    (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal - ε <
      (magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p by linarith))
  exact he.mono (fun _ h => h.le)

end InvariantIsing

end

end OAI
