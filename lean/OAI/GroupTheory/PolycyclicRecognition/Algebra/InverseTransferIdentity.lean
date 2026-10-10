import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseErrorBound

namespace OAI

/-! # The actual inverse-coefficient transfer

The inverse transfer is the negative inverse linear map applied to the
whole-fiber average. Its cocycle identity holds almost everywhere for each
fixed group element, exactly as required for an L² cocycle.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]

/-- The inverse-section transfer with its required inverse linear coefficient. -/
def inverseTheta (β : Measure G) (A : W ≃L[ℝ] W)
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (p : NormalizedPair G Λ) : W := -A.symm (inverseAveragedTransfer β π l φ p)

omit [CompleteSpace W] in
/-- The constructed inverse transfer belongs to the actual L² space. -/
theorem inverseTheta_memLp
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseTheta (normalizedRestriction m B) A π l φ) 2 ν :=
  (A.symm.toContinuousLinearMap.comp_memLp'
    (inverseAveragedTransfer_memLp m μ ν hprod π l hπ hl hφ hB hB0)).neg

/-- The inverse transfer identity is derived on almost every fiber, with no
assertion of a simultaneous exceptional set for all group elements. -/
theorem inverseTheta_identity_ae
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (y : G) :
    ∀ᵐ p ∂ν, pairHeight π y p +
      inverseTheta (normalizedRestriction m B) A π l φ (normalizedTranslate y p) -
      inverseTheta (normalizedRestriction m B) A π l φ p =
      A.symm (π y).toAdd - A.symm (inverseAverageError (normalizedRestriction m B) π l φ y p) := by
  let β := normalizedRestriction m B
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  have hD := inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0
  have hS := inverseFiberTransfer_shift_memLp ν β π l hl φ hD y
  have hDi := hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hSi := hS.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  filter_upwards [(integrable_prod_iff hDi.aestronglyMeasurable).mp hDi |>.1,
    (integrable_prod_iff hSi.aestronglyMeasurable).mp hSi |>.1] with p hpD hpS
  have h := inverseAveragedTransfer_identity β π l φ y p hpS hpD
  rw [hlA] at h
  exact inverse_transfer_linear_coefficient A h

/-- The actual inverse-height cocycle after adding the inverse transfer. -/
def inverseCocycleError (β : Measure G) (A : W ≃L[ℝ] W)
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (y : G) (p : NormalizedPair G Λ) : W :=
  pairHeight π y p + inverseTheta β A π l φ (normalizedTranslate y p) -
    inverseTheta β A π l φ p - A.symm (π y).toAdd

/-- Squared inverse-cocycle errors have at most the squared operator norm
loss when compared with the averaged fiber error. -/
theorem inverseCocycleError_lintegral_le
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (y : G) :
    (∫⁻ p, ‖inverseCocycleError (normalizedRestriction m B) A π l φ y p‖ₑ ^ 2 ∂ν) ≤
      ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2 *
        ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν := by
  have hi := inverseTheta_identity_ae m μ ν hprod A π l hπ hl hlA hφ hB hB0 y
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2 *
        ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hi] with p hp
      have he : inverseCocycleError (normalizedRestriction m B) A π l φ y p =
          -A.symm (inverseAverageError (normalizedRestriction m B) π l φ y p) := by
        unfold inverseCocycleError
        rw [hp]
        abel
      rw [he, enorm_neg]
      let r := inverseAverageError (normalizedRestriction m B) π l φ y p
      have hn : ‖A.symm r‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖r‖ :=
        A.symm.toContinuousLinearMap.le_opNorm r
      simp only [← ofReal_norm]
      change (ENNReal.ofReal ‖A.symm r‖) ^ 2 ≤
        (ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖) ^ 2 * (ENNReal.ofReal ‖r‖) ^ 2
      rw [← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (mul_pow _ _ 2)
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- Compact-uniform vanishing of averaged fiber errors gives the same
vanishing for the actual inverse-coefficient cocycle. -/
theorem inverseCocycleError_tendsto_uniform
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    {B Q : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0)
    (hR : Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseCocycleError (normalizedRestriction m B) A π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0) := by
  let K := ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2
  have ht : Filter.Tendsto (fun n => K * (⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hR
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    refine (inverseCocycleError_lintegral_le m μ ν hprod A π l hπ hl hlA (hφ n) hB hB0 y).trans ?_
    apply mul_le_mul_right
    exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)

end PolycyclicRecognition

end

end OAI
