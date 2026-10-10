import OAI.Probability.InvariantIsing.Fields.FieldEntropySequence
import OAI.Probability.InvariantIsing.Fields.FieldPairingContinuity
import OAI.Probability.InvariantIsing.Fields.FieldPartitionSupport
import OAI.Probability.InvariantIsing.Spectral.SpectralPathLimit
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds

namespace OAI

/-! Identification of the entropy in the cavity limit. Approximate
self-consistency, with the actual scalar supporting inequality, makes the
finite field trials approach the entropy supremum. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem field_entropy_sequence (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0)) :
    entropyFunctional p ≠ ⊤ ∧
    Tendsto (fun n => fieldValue (h n) 0 + fieldPairing p (h n) / 2)
      atTop (𝓝 (entropyFunctional p).toReal) := by
  apply field_entropy_sequence_of_support p h hC _ hself
  intro n k
  simpa only [one_div, inv_mul_eq_div] using field_support (h n) k

theorem cavity_entropy_trial_tendsto {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    entropyFunctional p ≠ ⊤ ∧
    Tendsto (fun n => fieldValue (h n) 0 + fieldPairing (q n) (h n) / 2 +
      spectralFunctional (finiteR ρ eig hρ hsum) (q n)) atTop
      (𝓝 ((entropyFunctional p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p)) := by
  obtain ⟨htop, hent⟩ := field_entropy_sequence p h hC hself
  have hpair := field_pairing_path_tendsto p q h hC hq
  have hspec := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hsum p q hq zero_le_one
  simp only [finiteTemperatureFunctional_eq ρ eig hρ hsum _ zero_le_one, one_mul] at hspec
  refine ⟨htop, ?_⟩
  have ht := (hent.add (hpair.div_const 2)).add hspec
  have he : (fun n => (fieldValue (h n) 0 + fieldPairing p (h n) / 2 +
      (fieldPairing (q n) (h n) - fieldPairing p (h n)) / 2) +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) =
      (fun n => fieldValue (h n) 0 + fieldPairing (q n) (h n) / 2 +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) := by
    funext n
    ring
  rw [he] at ht
  simpa only [zero_div, add_zero] using ht

theorem cavity_entropy_trial_eventually_lower {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (variationalFunctional (finiteR ρ eig hρ hsum)).toReal - ε ≤
        fieldValue (h n) 0 + fieldPairing (q n) (h n) / 2 +
          spectralFunctional (finiteR ρ eig hρ hsum) (q n) := by
  obtain ⟨htop, ht⟩ := cavity_entropy_trial_tendsto ρ eig hρ hsum p q h hC hself hq
  have hbot : entropyFunctional p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (entropyFunctional_nonneg p)
  have hfinite := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hi := iInf_le (fun v : OverlapPath => entropyFunctional v +
    (spectralFunctional (finiteR ρ eig hρ hsum) v : EReal)) p
  change variationalFunctional (finiteR ρ eig hρ hsum) ≤ _ at hi
  rw [← EReal.coe_toReal hfinite.1 hfinite.2, ← EReal.coe_toReal htop hbot,
    ← EReal.coe_add] at hi
  have hi' : (variationalFunctional (finiteR ρ eig hρ hsum)).toReal ≤
      (entropyFunctional p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p := by
    exact_mod_cast hi
  intro ε hε
  have hclose := ht.eventually (lt_mem_nhds (show
      (variationalFunctional (finiteR ρ eig hρ hsum)).toReal - ε <
        (entropyFunctional p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p by linarith))
  exact hclose.mono (fun _ hn => hn.le)

end InvariantIsing

end

end OAI
