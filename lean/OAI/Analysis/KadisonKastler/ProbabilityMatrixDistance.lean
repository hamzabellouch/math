import OAI.Analysis.KadisonKastler.ProbabilityOperatorRelations
import OAI.Analysis.KadisonKastler.MeasurablePoisson
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import OAI.Analysis.KadisonKastler.CompleteAmplification
import OAI.Analysis.KadisonKastler.MatrixCommutantDistance

namespace OAI

/-! # Distance to an algebra after vector integration

Diagonal amplification commutes with the actual vector integral. Applying
the published complete commutant-distance bound to the commutant gives
an algebra approximation without choosing measurable nearest points.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixIntegralOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixIntegralStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
/-- Finite diagonal amplification preserves vector measurability. -/
theorem diagonalOperator_vector_measurable
    (μ : Measure S) (F : S → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ) (n : ℕ) :
    ∀ x : Generator.FiniteHilbert (Fin n) H,
      AEStronglyMeasurable (fun s => Generator.diagonalOperator (F s) x) μ := by
  intro x
  have he (s : S) : Generator.diagonalOperator (F s) x =
      ∑ i : Fin n, Generator.tupleSingle i (F s (x i)) := by
    simpa only [Generator.diagonalOperator_apply] using
      Generator.tuple_eq_sum_single (Generator.diagonalOperator (F s) x)
  simp_rw [he]
  convert (Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
    (Generator.tupleSingle i).continuous.comp_aestronglyMeasurable (hF (x i))) using 1
  funext s
  simp only [Finset.sum_apply]

theorem norm_diagonalOperator_le (T : H →L[ℂ] H) (n : ℕ) :
    ‖Generator.diagonalOperator (ι := Fin n) T‖ ≤ ‖T‖ := by
  rw [← hilbertMatrix_diagonalAmplification_eq, norm_hilbertMatrix]
  exact norm_diagonalAmplification_le T

theorem probabilityOperatorIntegral_diagonal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (n : ℕ) :
    probabilityOperatorIntegral μ (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
      (diagonalOperator_vector_measurable μ F hF n) C
      (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs) =
      Generator.diagonalOperator (probabilityOperatorIntegral μ F hF C hC) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change (∫ s, Generator.diagonalOperator (ι := Fin n) (F s) x ∂μ) i = ∫ s, F s (x i) ∂μ
  have hi := integrable_bounded_operator_vector μ
    (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
    (diagonalOperator_vector_measurable μ F hF n)
    (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs) x
  let p : Generator.FiniteHilbert (Fin n) H →L[ℂ] H := PiLp.proj 2 (fun _ : Fin n => H) i
  exact (p.integral_comp_comm hi).symm

/-- A matrix over the commutant commutes with each diagonal element of the algebra. -/
theorem diagonal_commutes_commutant_matrix (M : VonNeumannAlgebra H)
    (b : H →L[ℂ] H) (hb : b ∈ M) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (Algebra M.commutant)) :
    Generator.diagonalOperator b * matrixOperatorHom M.commutant X =
      matrixOperatorHom M.commutant X * Generator.diagonalOperator b := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [mul_apply_eq_comp, Generator.diagonalOperator_apply,
    matrixOperatorHom_apply, hilbertMatrix_apply, CStarMatrix.map_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun T : H →L[ℂ] H => T (x j))
    ((VonNeumannAlgebra.mem_commutant_iff.mp (X i j).property) b hb)

local instance integralSourceOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance integralSourceStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Pointwise algebra distance bounds pass to a complete commutator bound
for the integral against the algebra's commutant. -/
theorem probabilityOperatorIntegral_complete_commutant_bound
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ) :
    CompletelyBoundedBy
      ((innerDerivation (probabilityOperatorIntegral μ F hF C hC)).comp
        M.commutant.toStarSubalgebra.subtype.toLinearMap) (2 * δ) := by
  apply completelyBoundedBy_of_large_square
  intro n _ X
  have hd := norm_probabilityOperatorIntegral_commutator_of_near μ
    (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
    (diagonalOperator_vector_measurable μ F hF n) C
    (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs)
    (matrixOperatorHom M.commutant X) hδ ?_
  · rw [probabilityOperatorIntegral_diagonal, norm_matrixOperatorHom] at hd
    rw [← norm_hilbertMatrix, hilbertMatrix_map_innerDerivation,
      hilbertMatrix_diagonalAmplification_eq]
    exact hd
  · filter_upwards [hnear] with s hs
    obtain ⟨b, hb, hFb⟩ := hs
    refine ⟨Generator.diagonalOperator (ι := Fin n) b,
      diagonal_commutes_commutant_matrix M b hb n X, ?_⟩
    have he : Generator.diagonalOperator (ι := Fin n) (F s) -
        Generator.diagonalOperator b = Generator.diagonalOperator (F s - b) := by
      apply ContinuousLinearMap.ext
      intro x
      apply PiLp.ext
      intro i
      rfl
    rw [he]
    exact (norm_diagonalOperator_le (F s - b) n).trans hFb

/-- The published complete commutant-distance theorem supplies the needed
algebra distance after integration, without any measurable selection. -/
theorem exists_algebra_approximation_probabilityOperatorIntegral
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ)
    (r : ℝ) (hr : δ < r) :
    ∃ b : H →L[ℂ] H, b ∈ M ∧
      ‖probabilityOperatorIntegral μ F hF C hC - b‖ < r := by
  obtain ⟨b, hb, hclose⟩ := exists_commutant_approximation_of_complete_bound M.commutant
    hDistance (probabilityOperatorIntegral μ F hF C hC) (mul_nonneg (by norm_num) hδ)
    (probabilityOperatorIntegral_complete_commutant_bound μ F hF C hC M hδ hnear)
    r (by linarith)
  exact ⟨b, by simpa only [VonNeumannAlgebra.commutant_commutant] using hb, hclose⟩

/-- Algebra distance is not increased by the vectorwise probability integral. -/
theorem infDist_probabilityOperatorIntegral_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, Metric.infDist (F s) (M : Set (H →L[ℂ] H)) ≤ δ) :
    Metric.infDist (probabilityOperatorIntegral μ F hF C hC)
      (M : Set (H →L[ℂ] H)) ≤ δ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ + ε / 2 := by
    filter_upwards [hnear] with s hs
    obtain ⟨b, hb, hFb⟩ := (Metric.infDist_lt_iff ⟨0, M.zero_mem⟩).mp
      (hs.trans_lt (show δ < δ + ε / 2 by linarith))
    exact ⟨b, hb, by simpa only [dist_eq_norm] using hFb.le⟩
  obtain ⟨b, hb, hFb⟩ := exists_algebra_approximation_probabilityOperatorIntegral
    μ F hF C hC M hDistance (by positivity : 0 ≤ δ + ε / 2) hn
    (δ + ε) (by linarith)
  exact (Metric.infDist_le_dist_of_mem hb).trans
    (by simpa only [dist_eq_norm] using hFb.le)

/-- The positive Poisson kernel retains an essential algebra-distance bound
at every point above the real axis. -/
theorem infDist_measurablePoissonAverage_le
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s, Metric.infDist (F s) (M : Set (H →L[ℂ] H)) ≤ δ)
    (t r : ℝ) (hr : 0 < r) :
    Metric.infDist (measurablePoissonAverage F hF C hC t r hr)
      (M : Set (H →L[ℂ] H)) ≤ δ :=
  infDist_probabilityOperatorIntegral_le _ F _ C _ M hDistance hδ
    ((cauchyMeasure_absolutelyContinuous t hr).ae_le hnear)

/-- Scalar multiplication scales distance to the concrete complex algebra. -/
theorem infDist_smul_algebra (M : VonNeumannAlgebra H) (z : ℂ)
    (T : H →L[ℂ] H) :
    Metric.infDist (z • T) (M : Set (H →L[ℂ] H)) =
      ‖z‖ * Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [zero_smul, norm_zero, zero_mul]
    exact Metric.infDist_zero_of_mem M.zero_mem
  · have hset : z • (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := by
      ext y
      simp only [Set.mem_smul_set]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact M.toStarSubalgebra.smul_mem hx z
      · intro hy
        refine ⟨z⁻¹ • y, M.toStarSubalgebra.smul_mem hy z⁻¹, ?_⟩
        rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    have he := infDist_smul₀ hz (M : Set (H →L[ℂ] H)) T
    rwa [hset] at he

end

end KadisonKastler

end OAI
