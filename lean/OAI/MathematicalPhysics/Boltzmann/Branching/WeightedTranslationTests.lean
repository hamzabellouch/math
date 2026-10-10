import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment

namespace OAI

/-! # Uniformly bounded tests against small translations of an L1 pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance weightedTranslationHaar : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem weighted_translation_identity (ρ φ : Velocity × Velocity → ℝ) (a : Velocity × Velocity) :
    (∫ p, ρ p*φ (p+a)) = ∫ p, ρ (p-a)*φ p := by
  simpa only [add_sub_cancel_right] using
    (integral_add_right_eq_self (fun p => ρ (p-a)*φ p) a)

theorem weighted_translation_difference {ρ φ : Velocity × Velocity → ℝ}
    (hρ : Integrable ρ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ p, |φ p| ≤ C)
    (a : Velocity × Velocity) :
    (∫ p, ρ p*(φ (p+a)-φ p)) = ∫ p, φ p*(ρ (p-a)-ρ p) := by
  have hshift : Integrable (fun p => ρ (p-a)) := hρ.comp_sub_right a
  have hA : Integrable (fun p => ρ p*φ (p+a)) := by
    apply (hρ.bdd_mul (hφ.comp (measurable_id.add_const a)).aestronglyMeasurable
      (ae_of_all _ (fun p => hC (p+a)))).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have hB : Integrable (fun p => ρ p*φ p) := by
    apply (hρ.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have hD : Integrable (fun p => φ p*ρ (p-a)) :=
    hshift.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)
  have hE : Integrable (fun p => φ p*ρ p) :=
    hρ.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)
  calc
    _ = (∫ p, ρ p*φ (p+a))-(∫ p, ρ p*φ p) := by
      simp_rw [mul_sub]
      exact integral_sub hA hB
    _ = (∫ p, φ p*ρ (p-a))-(∫ p, φ p*ρ p) := by
      rw [weighted_translation_identity]
      simp_rw [mul_comm]
    _ = _ := by
      simp_rw [mul_sub]
      exact (integral_sub hD hE).symm

theorem weighted_translation_tests_zero {ρ : Velocity × Velocity → ℝ}
    (hρm : Measurable ρ) (hρ : Integrable ρ) {a : ℕ → Velocity × Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {φ : ℕ → Velocity × Velocity → ℝ}
    (hφ : ∀ n, Measurable (φ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n p, |φ n p| ≤ C) :
    Tendsto (fun n => ∫ p, ρ p*(φ n (p+a n)-φ n p)) atTop (𝓝 0) := by
  let f : ℕ → Velocity × Velocity → ℝ := fun n p => ρ (p-a n)-ρ p
  have hfm n : Measurable (f n) := (hρm.comp (measurable_id.sub_const (a n))).sub hρm
  have hfi n : Integrable (f n) := (hρ.comp_sub_right (a n)).sub hρ
  have hL : Tendsto (fun n => eLpNorm (f n) 1 volume) atTop (𝓝 0) := by
    have han : Tendsto (fun n => -a n) atTop (𝓝 0) := by simpa only [neg_zero] using ha.neg
    have ht := (pair_translation_L1 hρ 0).comp han
    simpa only [Function.comp_def,sub_eq_add_neg,add_zero,neg_zero,f] using ht
  have hb := Compactness.tendsto_L1_bounded_mul_zero
    (fun n => (hfm n).aestronglyMeasurable) (fun n => (hφ n).aestronglyMeasurable)
    hL hC (Filter.Eventually.of_forall (fun n => ae_of_all _ (hbound n)))
  have hi n : Integrable (fun p => φ n p*f n p) :=
    (hfi n).bdd_mul (hφ n).aestronglyMeasurable (ae_of_all _ (hbound n))
  have ht : Tendsto (fun n => ∫ p, φ n p*f n p) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_L1' (fun _ : Velocity × Velocity => (0:ℝ))
      (Filter.Eventually.of_forall hi) (by
        change Tendsto (fun n => eLpNorm (fun p => φ n p*f n p-0) 1 volume) atTop (𝓝 0)
        simpa only [sub_zero] using hb)
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n => (weighted_translation_difference hρ (hφ n) (hbound n) (a n)).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
