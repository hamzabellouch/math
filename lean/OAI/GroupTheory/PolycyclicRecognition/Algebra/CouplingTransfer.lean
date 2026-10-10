import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseSection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PairHeightCocycle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! # Transfer functions in the two coupling charts

The transfer is lifted by adding target height. Its domain defect is the
original stationary cocycle defect. In inverse coordinates, differences
inside a fiber are the same defects, and fiber averaging gives the exact
inverse transfer identity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [NormedAddCommGroup W]

/-- Extend a section transfer by target-height equivariance. -/
def pairTransferLift (π : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (q : G × NormalizedPair G Λ) : W :=
  (π q.1).toAdd + φ q.2

/-- The stationary domain defect, with the proposed mean height subtracted. -/
def pairTransferDefect (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (t : G) (p : NormalizedPair G Λ) : W :=
  pairHeight π t p + φ (normalizedTranslate t p) - φ p - (l t).toAdd

/-- In inverse coordinates, subtract the proposed domain height. -/
def inverseFiberTransfer (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (q : NormalizedPair G Λ × G) : W :=
  pairTransferLift π φ (pairChartTransition.symm q) - (l q.2).toAdd

omit [ProperSpace G] in
theorem pairTransferLift_domain (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (t : G) (q : G × NormalizedPair G Λ) :
    pairTransferLift π φ (pairDomainTranslation t q) - pairTransferLift π φ q -
      (l t).toAdd = pairTransferDefect π l φ t q.2 := by
  simp only [pairTransferLift, pairDomainTranslation, pairTransferDefect, pairHeight,
    map_mul π, toAdd_mul]
  abel

/-- The inverse chart intertwines domain translation with right translation
inside each fiber. -/
theorem pairChartTransition_symm_domain (t : G) (q : NormalizedPair G Λ × G) :
    pairDomainTranslation t (pairChartTransition.symm q) =
      pairChartTransition.symm (q.1, q.2 * t) := by
  apply pairChartTransition.injective
  rw [pairChartTransition_domain, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- Differences of two fiber values are original cocycle defects. -/
theorem inverseFiberTransfer_sub (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (p : NormalizedPair G Λ) (x₁ x₂ : G) :
    inverseFiberTransfer π l φ (p, x₁) - inverseFiberTransfer π l φ (p, x₂) =
      pairTransferDefect π l φ (x₂⁻¹ * x₁)
        (pairChartTransition.symm (p, x₂)).2 := by
  have h := pairTransferLift_domain π l φ (x₂⁻¹ * x₁)
    (pairChartTransition.symm (p, x₂))
  rw [pairChartTransition_symm_domain, mul_inv_cancel_left] at h
  simp only [inverseFiberTransfer, map_mul l, map_inv l, toAdd_mul, toAdd_inv] at *
  rw [← h]
  abel

/-- Target translation in the inverse chart, expressed back in target
coordinates. -/
theorem pairChartTransition_symm_target (y : G) (q : NormalizedPair G Λ × G) :
    pairChartTransition.symm (pairInverseTargetTranslation y q) =
      (y⁻¹ * (pairChartTransition.symm q).1, (pairChartTransition.symm q).2) := by
  apply pairChartTransition.injective
  rw [Homeomorph.apply_symm_apply, pairChartTransition_target,
    Homeomorph.apply_symm_apply]

/-- The pointwise target transfer identity before averaging. -/
theorem inverseFiberTransfer_target (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (q : NormalizedPair G Λ × G) :
    inverseFiberTransfer π l φ (pairInverseTargetTranslation y q) =
      inverseFiberTransfer π l φ q - (π y).toAdd + (l (q.1.val.1 y)).toAdd := by
  unfold inverseFiberTransfer
  rw [pairChartTransition_symm_target]
  simp only [pairTransferLift, pairInverseTargetTranslation,
    map_mul π, map_inv π, map_mul l, map_inv l, toAdd_mul, toAdd_inv]
  abel

/-- A version with a fixed integration coordinate, suitable for averaging. -/
theorem inverseFiberTransfer_normalizedTranslate (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (p : NormalizedPair G Λ) (x : G) :
    inverseFiberTransfer π l φ (normalizedTranslate y p, x) =
      inverseFiberTransfer π l φ (p, p.val.1 y * x) -
        (π y).toAdd + (l (p.val.1 y)).toAdd := by
  simpa only [pairInverseTargetTranslation, inv_mul_cancel_left] using
    inverseFiberTransfer_target π l φ y (p, p.val.1 y * x)

variable [MeasurableSpace G] [NormedSpace ℝ W] [CompleteSpace W]

/-- Average the transfer over a whole probability fiber. -/
def inverseAveragedTransfer (β : Measure G) (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (p : NormalizedPair G Λ) : W :=
  ∫ x, inverseFiberTransfer π l φ (p, x) ∂β

/-- The error is the average of differences inside one fiber. -/
def inverseAverageError (β : Measure G) (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (p : NormalizedPair G Λ) : W :=
  ∫ x, inverseFiberTransfer π l φ (p, p.val.1 y * x) -
    inverseFiberTransfer π l φ (p, x) ∂β

/-- Averaging yields the exact inverse-transfer identity; integrability is
required only on the two regions actually being averaged. -/
theorem inverseAveragedTransfer_identity (β : Measure G) [IsProbabilityMeasure β]
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (y : G) (p : NormalizedPair G Λ)
    (h₁ : Integrable (fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x)) β)
    (h₂ : Integrable (fun x => inverseFiberTransfer π l φ (p, x)) β) :
    inverseAveragedTransfer β π l φ (normalizedTranslate y p) -
      inverseAveragedTransfer β π l φ p =
      -(π y).toAdd + (l (p.val.1 y)).toAdd + inverseAverageError β π l φ y p := by
  unfold inverseAveragedTransfer inverseAverageError
  simp_rw [inverseFiberTransfer_normalizedTranslate]
  rw [integral_add (f := fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x) - (π y).toAdd) (h₁.sub (integrable_const ((π y).toAdd)))
      (integrable_const ((l (p.val.1 y)).toAdd)),
    integral_sub (f := fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x)) h₁ (integrable_const ((π y).toAdd)), integral_const, integral_const,
    integral_sub h₁ h₂]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  abel

end PolycyclicRecognition

end

end OAI
