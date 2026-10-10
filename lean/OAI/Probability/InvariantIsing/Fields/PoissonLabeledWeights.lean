import OAI.Probability.InvariantIsing.Fields.PoissonScaledWeights

namespace OAI

/-! Positive rescaling cannot merge active labeled Poisson points. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

lemma labeledPoisson_scaled_pair (μ : ℕ → FiniteMeasure ℝ)
    [∀ n, NullSingletonClass (μ n : Measure ℝ)]
    (a b : ChildLabel) (hab : a ≠ b) (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ ω ∂labeledPoissonLaw μ,
      a.2 < (ω a.1).1 → b.2 < (ω b.1).1 → c * (ω a.1).2 a.2 ≠ d * (ω b.1).2 b.2 := by
  have hev (m : ℕ) := measurePreserving_eval_infinitePi
    (fun j => finitePoissonCloud (μ j).mass ((μ j).normalize : Measure ℝ)) m
  by_cases ha : μ a.1 = 0
  · have hno : ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (μ a.1).mass
        ((μ a.1).normalize : Measure ℝ), ¬ a.2 < p.1 := by
      rw [ha]
      exact finitePoissonCloud_zero_inactive a.2
    exact ((hev a.1).quasiMeasurePreserving.tendsto_ae.eventually hno).mono
      (fun ω hω hactive _ => (hω hactive).elim)
  by_cases hb : μ b.1 = 0
  · have hno : ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (μ b.1).mass
        ((μ b.1).normalize : Measure ℝ), ¬ b.2 < p.1 := by
      rw [hb]
      exact finitePoissonCloud_zero_inactive b.2
    exact ((hev b.1).quasiMeasurePreserving.tendsto_ae.eventually hno).mono
      (fun ω hω _ hactive => (hω hactive).elim)
  by_cases hm : a.1 = b.1
  · have hij : a.2 ≠ b.2 := fun h => hab (Prod.ext hm h)
    have h := finitePoissonCloud_scaled_distinct (μ a.1) ha a.2 b.2 hij c d hd
    exact ((hev a.1).quasiMeasurePreserving.tendsto_ae.eventually h).mono
      (fun ω hω _ _ => by simpa only [hm] using hω)
  · have hp : MeasurePreserving (fun ω : WeightCloud => (ω a.1,ω b.1))
        (labeledPoissonLaw μ)
        ((finitePoissonCloud (μ a.1).mass ((μ a.1).normalize : Measure ℝ)).prod
          (finitePoissonCloud (μ b.1).mass ((μ b.1).normalize : Measure ℝ))) :=
      ⟨by fun_prop, Measure.infinitePi_map_eval_prod hm⟩
    have hq := ((finitePoissonCloud_point_law (μ a.1) a.2).prod
      (finitePoissonCloud_point_law (μ b.1) b.2)).comp hp
    let : NullSingletonClass ((μ b.1).normalize : Measure ℝ) :=
      finiteMeasure_normalize_noAtoms _ hb
    exact (hq.quasiMeasurePreserving.tendsto_ae.eventually
      (independent_scaled_ne _ _ c d hd)).mono (fun _ h _ _ => h)

lemma labeledPoisson_scaled_distinct (μ : ℕ → FiniteMeasure ℝ)
    [∀ n, NullSingletonClass (μ n : Measure ℝ)]
    (c : ChildLabel → ℝ) (hc : ∀ a, c a ≠ 0) :
    ∀ᵐ ω ∂labeledPoissonLaw μ, ∀ a b : ChildLabel,
      a.2 < (ω a.1).1 → b.2 < (ω b.1).1 →
      c a * (ω a.1).2 a.2 = c b * (ω b.1).2 b.2 → a = b := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  by_cases h : a = b
  · exact ae_of_all _ (fun _ _ _ _ => h)
  · exact (labeledPoisson_scaled_pair μ a b h (c a) (c b) (hc b)).mono
      (fun _ hh ha hb he => (hh ha hb he).elim)

instance intensityComponents_noAtoms (b : ℝ) (m : ℕ) :
    NullSingletonClass (intensityComponents (powerIntensity b) m : Measure ℝ) where
  measure_singleton x := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ powerIntensity b {x} := sfiniteSeq_le _ _ _
      _ = 0 := measure_singleton x

end InvariantIsing

end

end OAI
