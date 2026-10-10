import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchCover
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness

namespace OAI

/-! # Bounded incoming weights preserve the actual normalized-gain translation estimate -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weighted_normalizedGain_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    {w : X × (Velocity × Velocity) → ℝ} (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ z, |w z| ≤ K) {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |pairGain (fun z => w z*normalizedPair volume (f n) z) (p.1,p.2+a n)-
        pairGain (fun z => w z*normalizedPair volume (f n) z) p| ∂μ.prod volume) atTop (𝓝 0) := by
  let g := fun n => normalizedPair volume (f n)
  have hgm n : Measurable (g n) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)
  have hmi n : Integrable (momentPair (g n)) (μ.prod (volume : Measure (Velocity × Velocity))) := by
    have hh := weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
    rw [← Measure.volume_eq_prod] at hh
    exact hh
  have hmul (u : X × (Velocity × Velocity) → ℝ) :
      momentPair (fun z => w z*u z) = fun z => w z*momentPair u z := by
    funext z
    unfold momentPair
    ring
  apply pairGain_translation_of_moment_approximation (fun n => hw.mul (hgm n))
    (fun n => by
      change Integrable (momentPair (fun z => w z*g n z)) (μ.prod volume)
      rw [hmul]
      exact (hmi n).bdd_mul hw.aestronglyMeasurable (ae_of_all _ hK)) _ ha
  intro δ hδ
  let ρ := δ/((K:ℝ)+1)
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  obtain ⟨R,hR,B,u,hum,huB,hus,herr⟩ := normalizedPair_bounded_moment_approximation
    hfm hf hi hb (ENNReal.ofReal_pos.mpr hρ)
  refine ⟨R,hR,K*B,(fun n z => w z*u n z),fun n => hw.mul (hum n),?_,?_,?_⟩
  · intro n z
    rw [abs_mul,NNReal.coe_mul]
    exact mul_le_mul (hK z) (huB n z) (abs_nonneg _) K.coe_nonneg
  · intro n z hz
    change w z*u n z = 0
    rw [hus n z hz,mul_zero]
  · intro n
    change eLpNorm (momentPair (fun z => w z*g n z-w z*u n z)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ENNReal.ofReal δ
    have he : momentPair (fun z => w z*g n z-w z*u n z) =
        fun z => w z*momentPair (fun y => g n y-u n y) z := by
      funext z
      unfold momentPair
      ring
    rw [he]
    have hm := momentPair_measurable ((hgm n).sub (hum n))
    have hn : eLpNorm (fun z => w z*momentPair (fun y => g n y-u n y) z) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) ≤
        ENNReal.ofReal (K:ℝ)*eLpNorm (momentPair (fun y => g n y-u n y)) 1
          (μ.prod (volume : Measure (Velocity × Velocity))) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hw.mul hm).aestronglyMeasurable
      filter_upwards [] with z
      change ‖w z*momentPair (fun y => g n y-u n y) z‖ ≤
        (K:ℝ)*‖momentPair (fun y => g n y-u n y) z‖
      rw [norm_mul,Real.norm_eq_abs (w z)]
      exact mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _)
    have hsmall : (K:ℝ)*ρ ≤ δ := by
      dsimp only [ρ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < (K:ℝ)+1)).mpr
      nlinarith [K.coe_nonneg]
    exact hn.trans ((mul_le_mul' le_rfl (herr n)).trans (by
      rw [← ENNReal.ofReal_mul K.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal hsmall))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
