import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

section

/-! # Scalar majorants for the gain discrepancy of two positive profiles -/
namespace BoltzmannNonuniqueness.Compactness

theorem normalized_difference_abs_le {a b u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(a-b)/(1+u+v)| ≤ |a-b| := by
  rw [abs_div,abs_of_pos (by positivity : 0 < 1+u+v)]
  exact div_le_self (abs_nonneg _) (by linarith)

theorem normalized_difference_source_bound {a b u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(a-b)/(1+u+v)| ≤ a/(1+u)+b/(1+v) := by
  have hd : 0 < 1+u+v := by positivity
  calc
    _ = |a-b|/(1+u+v) := by rw [abs_div,abs_of_pos hd]
    _ ≤ (a+b)/(1+u+v) := by
      apply div_le_div_of_nonneg_right _ hd.le
      simpa only [abs_of_nonneg ha,abs_of_nonneg hb] using abs_sub a b
    _ = a/(1+u+v)+b/(1+u+v) := add_div _ _ _
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left ha (by positivity) (by linarith))
      (div_le_div_of_nonneg_left hb (by positivity) (by linarith))

end BoltzmannNonuniqueness.Compactness


end

section

/-! # The linear normalized-pair gain is the physical gain divided by spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem normalizedPair_postRate (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate (normalizedPair volume f) z = massNormalizedPostRate f z := by
  change pairPreRate (normalizedPair volume f) (scatterTriple z) =
    massNormalizedPreRate f (scatterTriple z)
  exact (massNormalizedPreRate_eq_pair f (scatterTriple z)).symm

theorem normalizedPair_gain (f : X × Velocity → ℝ) (p : X × Velocity) :
    pairGain (normalizedPair volume f) p = gainDensity f p/(1+fiberMass volume f p.1) := by
  unfold pairGain
  simp_rw [normalizedPair_postRate]
  change (∫ q : Velocity × Sphere,
    postRate f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  rfl

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Strong convergence of full normalized gains from their localized limits -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedGain_strong_of_localized
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (hgb : (∫ p, entropyGauge g p ∂μ.prod volume) ≤ C)
    {ν : Measure (X × Velocity)} (hν : ν ≤ μ.prod volume)
    (hc : ∀ η : C(Velocity,ℝ), HasCompactSupport η →
      Tendsto (fun n => eLpNorm
        (localizedPhysicalGain η (f n)-localizedPhysicalGain η g) 1 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (pairGain (normalizedPair volume (f n))-pairGain (normalizedPair volume g)) 1 ν)
      atTop (𝓝 0) := by
  choose η hηc hη0 hη1 hηeq using
    (fun j : ℕ => exists_velocity_unit_cutoff (show 0 < (j:ℝ)+1 by positivity))
  have hδ : Tendsto (fun j : ℕ => sphereArea univ*ENNReal.ofReal (8*C/((j:ℝ)+1)))
      atTop (𝓝 0) := by
    have he : Tendsto (fun j : ℕ => 8*C/((j:ℝ)+1)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have ht := ENNReal.Tendsto.const_mul (a := sphereArea univ) (ENNReal.tendsto_ofReal he)
      (Or.inr (measure_ne_top sphereArea univ))
    simpa only [ENNReal.ofReal_zero,mul_zero] using ht
  apply strongL1_of_two_sided_approximations hδ
    (u := fun j n => localizedPhysicalGain (η j) (f n))
    (v := fun j => localizedPhysicalGain (η j) g)
  · intro j n
    exact (eLpNorm_mono_measure _ hν).trans
      (localizedGain_tail_le (by positivity) (η j) (hη0 j) (hη1 j) (hηeq j)
        (hfm n) (hf n) (hi n) (hb n))
  · intro j
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono_measure _ hν).trans
      (localizedGain_tail_le (by positivity) (η j) (hη0 j) (hη1 j) (hηeq j) hgm hg hgi hgb)
  · exact fun j => hc (η j) (hηc j)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
