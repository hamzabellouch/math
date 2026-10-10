import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE

namespace OAI

/-! # A common velocity translation modulus for the physical gain sequence -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem uniform_zero_of_all_velocity_sequences {F : ℕ → Velocity → ℝ}
    (h : ∀ (i : ℕ → ℕ) (a : ℕ → Velocity), Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => F (i n) (a n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n a, ‖a‖ < δ → |F n a| < ε := by
  classical
  by_contra hh
  push Not at hh
  have hb (k : ℕ) : ∃ n a, ‖a‖ < 1/((k:ℝ)+1) ∧ ε ≤ |F n a| :=
    hh (1/((k:ℝ)+1)) (by positivity)
  choose i a ha hbad using hb
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hat : Tendsto a atTop (𝓝 0) :=
    squeeze_zero_norm' (Eventually.of_forall (fun k => (ha k).le)) ht
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (h i a hat) ε hε
  have hn := hN N le_rfl
  rw [Real.dist_eq,sub_zero] at hn
  exact (not_lt_of_ge (hbad N)) hn

open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_uniform_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n a, ‖a‖ < δ →
      (∫ p, |localizedPhysicalGain η (f n) (p.1,p.2+a)-localizedPhysicalGain η (f n) p|
        ∂μ.prod volume) < ε := by
  obtain ⟨δ,hδ,hsmall⟩ := uniform_zero_of_all_velocity_sequences
    (F := fun n a => ∫ p,
      |localizedPhysicalGain η (f n) (p.1,p.2+a)-localizedPhysicalGain η (f n) p|
      ∂μ.prod volume)
    (fun i a ha => localizedGain_translation (μ := μ) (fun n => hfm (i n))
      (fun n => hf (i n)) (fun n => hi (i n)) (fun n => hb (i n)) η hη ha) ε hε
  refine ⟨δ,hδ,fun n a ha => ?_⟩
  simpa only [abs_of_nonneg (integral_nonneg (fun p => abs_nonneg _))] using hsmall n a ha

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
