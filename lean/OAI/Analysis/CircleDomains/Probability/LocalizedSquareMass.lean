import OAI.Analysis.CircleDomains.Probability.DensityMassBound
import Mathlib.MeasureTheory.Measure.Continuity

namespace OAI

/-! Local square-density estimates for point avoidance. The energy of a
shrinking family tends to zero when its intersection is reference-null. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem localized_square_mass_bound (σ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) {A : Set X} (hA : MeasurableSet A) :
    ((σ.withDensity g) A) ^ 2 ≤ (∫⁻ x in A, g x ^ 2 ∂σ) * σ A := by
  have h := mass_le_densityMassBound (σ.restrict A) hg
    (le_refl (∫⁻ x, g x ^ 2 ∂σ.restrict A))
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [withDensity_apply _ hA]
  apply (pow_le_pow_left' h 2).trans_eq
  rw [densityMassBound, mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

theorem tendsto_local_square_energy_zero (σ : Measure X) {g : X → ℝ≥0∞}
    (hgfin : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hnull : σ (⋂ n, A n) = 0) :
    Tendsto (fun n => ∫⁻ x in A n, g x ^ 2 ∂σ) atTop (𝓝 0) := by
  let ν := σ.withDensity (fun x => g x ^ 2)
  have hfin : ν univ < ∞ := by
    rw [show ν = σ.withDensity (fun x => g x ^ 2) from rfl,
      withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact hgfin
  have hν : IsFiniteMeasure ν := ⟨hfin⟩
  have hz : ν (⋂ n, A n) = 0 := withDensity_absolutelyContinuous σ _ hnull
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [hz] at ht
  simpa only [Function.comp_def, ν, withDensity_apply _ (hA _)] using ht

end CircleDomainRigidity

end

end OAI
