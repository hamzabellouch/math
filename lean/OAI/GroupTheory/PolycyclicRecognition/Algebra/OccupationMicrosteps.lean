import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairMicrosteps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairLabelFunctions
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Microstep estimates under dominated occupation laws

The sampling calculation supplies domination of the translated laws. This
file applies that domination to the exact normalized height increments.
-/

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped NNReal BigOperators

/-- Domination of a pushed sampling law controls every nonnegative continuous
observable on the compact section. -/
theorem integral_comp_le_of_map_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (σ μ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (T : X → X) (hT : Continuous T) {c : ℝ≥0}
    (hdom : Measure.map T σ ≤ c • μ)
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    ∫ x, f (T x) ∂σ ≤ (c : ℝ) * ∫ x, f x ∂μ := by
  calc
    _ = ∫ x, f x ∂Measure.map T σ :=
      (integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ ≤ ∫ x, f x ∂c • μ := integral_mono_measure hdom
      (Filter.Eventually.of_forall hpos)
      (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- The mean convex error of a long increment is bounded by one fixed-length
occupation observable and the explicit final-step error. -/
theorem integral_normalized_microsteps_le
    (σ μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure σ] [IsProbabilityMeasure μ]
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g h : G) (n : ℕ) {c : ℝ≥0}
    (hdom : ∀ j : Fin n, Measure.map (fun p : NormalizedPair G Λ => (g ^ (j : ℕ))⁻¹ • p) σ ≤ c • μ)
    {L t D : ℝ} (hL : 0 < L) (ht : 0 < t) (hD : 0 ≤ D)
    (hn : (n : ℝ) * L ≤ t) (hn' : t ≤ ((n : ℝ) + 1) * L)
    (hrem : dist 1 h ≤ D * L)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    ∫ p, infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ∂σ ≤
      (c : ℝ) * (∫ p, infDist (L⁻¹ • pairHeight π g p) S ∂μ) +
        (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖) := by
  let d : NormalizedPair G Λ → ℝ := fun p => infDist (L⁻¹ • pairHeight π g p) S
  have hd : Continuous d := continuous_pair_label_distance π hπ.continuous g L S
  have hj (j : Fin n) :
      ∫ p, d ((g ^ (j : ℕ))⁻¹ • p) ∂σ ≤ (c : ℝ) * ∫ p, d p ∂μ :=
    integral_comp_le_of_map_le σ μ _ (continuous_const_smul _) (hdom j) d hd
      (fun _ => infDist_nonneg)
  have hji (j : Fin n) : Integrable (fun p => d ((g ^ (j : ℕ))⁻¹ • p)) σ :=
    (hd.comp (continuous_const_smul _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft := (continuous_pair_label_distance π hπ.continuous (g ^ n * h) t
    (convexHull ℝ S)).integrable_of_hasCompactSupport (μ := σ)
      (HasCompactSupport.of_compactSpace _)
  have hsumI : Integrable (fun p => ∑ j : Fin n, d ((g ^ (j : ℕ))⁻¹ • p)) σ :=
    integrable_finsetSum Finset.univ (fun j _ => hji j)
  let E := (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖)
  have hb := integral_mono hleft ((hsumI.const_mul (L / t)).add (integrable_const E))
    (fun p => normalized_pair_microsteps_convex_bound_of_remainder
      π hπ g h p n hL ht hD hn hn' hrem hS hw₀)
  simp only [Pi.add_apply] at hb
  rw [integral_add (hsumI.const_mul _) (integrable_const E), integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hji j), integral_const] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
  have hcoef : (L / t) * (n : ℝ) ≤ 1 := by
    rw [mul_comm, ← mul_div_assoc]
    exact (div_le_one ht).mpr hn
  have hI : 0 ≤ (c : ℝ) * ∫ p, d p ∂μ :=
    mul_nonneg c.coe_nonneg (integral_nonneg (fun _ => infDist_nonneg))
  apply hb.trans
  apply add_le_add _ le_rfl
  calc
    (L / t) * ∑ j : Fin n, ∫ p, d ((g ^ (j : ℕ))⁻¹ • p) ∂σ
        ≤ (L / t) * ∑ _j : Fin n, (c : ℝ) * ∫ p, d p ∂μ :=
          mul_le_mul_of_nonneg_left hsum (div_pos hL ht).le
    _ = ((L / t) * (n : ℝ)) * ((c : ℝ) * ∫ p, d p ∂μ) := by simp; ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hcoef hI

end PolycyclicRecognition

end OAI
