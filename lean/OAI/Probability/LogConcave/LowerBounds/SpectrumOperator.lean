import Mathlib
import OAI.Probability.LogConcave.LowerBounds.WeightedEvaluation

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound

theorem diagonalStatistic_eq_dotProduct {d : ℕ} (c u : Fin d → ℝ) :
    diagonalStatistic c u = dotProduct u (Matrix.diagonal c *ᵥ u) := by
  simp only [diagonalStatistic, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem normStatistic_eq_dotProduct {d : ℕ} (u : Fin d → ℝ) :
    diagonalStatistic (fun _ => 1) u = dotProduct u u := by
  simp [diagonalStatistic, dotProduct, pow_two]

theorem separationThreshold_eq {d q : ℕ} (hd : 0 < d) :
    2 * blockTolerance d q * (2*d) = separationThreshold d q := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := Real.sq_sqrt hdr.le
  have hsn : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  unfold blockTolerance separationThreshold
  field_simp
  nlinarith

theorem algorithm_span_separation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d q : ℕ}
    (hqd : 4*q+1 < 2*d) (ht : blockTolerance d q ≤ 1/2)
    {rows : Ω → Fin d → Fin (q+1) → ℝ}
    (hrows : HasLaw rows (gaussianRows d (q+1)) P) (U : Ω → Fin d → ℝ)
    (hU : ∀ᵐ ω ∂P, U ω ∈ krylovSpace (rows ω)) :
    P.real {ω | U ω ∈ separationEvent d q} ≤ 1/100 := by
  obtain ⟨G,hG,hm,hgood⟩ := lower_span_statistic hqd ht
  have hsub : {ω | U ω ∈ separationEvent d q} ≤ᵐ[P] {ω | rows ω ∈ Gᶜ} := by
    filter_upwards [hU] with ω hu
    intro hsep
    change rows ω ∉ G
    intro hg
    have hstat := hgood (rows ω) hg (U ω) hu
    rw [← diagonalStatistic_eq_dotProduct, ← normStatistic_eq_dotProduct] at hstat
    have hn := hsep.1
    have hs := hsep.2
    have hbound : 2 * blockTolerance d q * diagonalStatistic (fun _ => 1) (U ω) ≤
        separationThreshold d q := by
      rw [← separationThreshold_eq (by omega : 0 < d)]
      exact mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) (blockTolerance_pos (q := q) (by omega : 0 < d)).le)
    exact (not_lt_of_ge (hstat.trans hbound)) hs
  have hmono := ENNReal.toReal_mono (measure_ne_top P {ω | rows ω ∈ Gᶜ})
    (measure_mono_ae hsub)
  change P.real {ω | U ω ∈ separationEvent d q} ≤ P.real {ω | rows ω ∈ Gᶜ} at hmono
  have hlaw : P.real {ω | rows ω ∈ Gᶜ} = (gaussianRows d (q+1)).real Gᶜ :=
    hrows.measureReal_eq hG.compl
  rw [hlaw, measureReal_compl hG, probReal_univ] at hmono
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace
open Matrix WithLp

def spectrumOperator (d : ℕ) : Point d →L[ℝ] Point d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (Matrix.diagonal (fun k : Fin d => eigenvalue d k))

@[simp] theorem spectrumOperator_apply {d : ℕ} (x : Point d) (k : Fin d) :
    spectrumOperator d x k = eigenvalue d k * x k := by
  change (Matrix.diagonal (fun k : Fin d => eigenvalue d k) *ᵥ ofLp x) k = _
  exact Matrix.mulVec_diagonal _ _ _

def quadraticOperator {d : ℕ} (O : Rotations d) : Point d →L[ℝ] Point d :=
  (rotationIsometry O).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((spectrumOperator d).comp (rotationIsometry O).symm.toContinuousLinearEquiv.toContinuousLinearMap)

def quadraticPotential {d : ℕ} (O : Rotations d) (x : Point d) : ℝ :=
  inner ℝ x (quadraticOperator O x) / 2

lemma spectrumOperator_symmetric (d : ℕ) :
    (spectrumOperator d).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (spectrumOperator d x) y = inner ℝ x (spectrumOperator d y)
  simp only [PiLp.inner_apply, Real.inner_apply, spectrumOperator_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma quadraticOperator_symmetric {d : ℕ} (O : Rotations d) :
    (quadraticOperator O).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ ((rotationIsometry O) (spectrumOperator d ((rotationIsometry O).symm x))) y =
    inner ℝ x ((rotationIsometry O) (spectrumOperator d ((rotationIsometry O).symm y)))
  rw [← (rotationIsometry O).apply_symm_apply y, ← (rotationIsometry O).apply_symm_apply x]
  simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  exact spectrumOperator_symmetric d _ _

lemma quadraticOperator_bounds {d : ℕ} (O : Rotations d) (x : Point d) :
    ‖x‖^2 ≤ inner ℝ x (quadraticOperator O x) ∧
      inner ℝ x (quadraticOperator O x) ≤ 2 * ‖x‖^2 := by
  let y := (rotationIsometry O).symm x
  have hinner : inner ℝ x (quadraticOperator O x) =
      ∑ k : Fin d, eigenvalue d k * (y k)^2 := by
    change inner ℝ x ((rotationIsometry O) (spectrumOperator d y)) = _
    rw [← (rotationIsometry O).apply_symm_apply x]
    simp only [LinearIsometryEquiv.inner_map_map, PiLp.inner_apply, Real.inner_apply,
      spectrumOperator_apply]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [y]
    ring
  have hnorm : ‖x‖^2 = ∑ k : Fin d, (y k)^2 := by
    rw [← (rotationIsometry O).symm.norm_map x, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  rw [hinner, hnorm, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro k _
    have hb := (eigenvalue_bounds d k).1
    nlinarith [sq_nonneg (y k)]
  · apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (eigenvalue_bounds d k).2 (sq_nonneg _)

lemma quadraticPotential_hasGradientAt {d : ℕ} (O : Rotations d) (x : Point d) :
    HasGradientAt (quadraticPotential O) (quadraticOperator O x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((hasFDerivAt_id x).inner ℝ (quadraticOperator O).hasFDerivAt).const_smul (1 / 2 : ℝ)
  convert! hd using 1
  · ext y
    simp only [quadraticPotential, Pi.smul_apply, smul_eq_mul, id_eq]
    ring
  ext y
  have hs := quadraticOperator_symmetric O x y
  change inner ℝ (quadraticOperator O x) y = inner ℝ x (quadraticOperator O y) at hs
  change inner ℝ (quadraticOperator O x) y =
    (1 / 2 : ℝ) * (inner ℝ x (quadraticOperator O y) + inner ℝ y (quadraticOperator O x))
  rw [← hs, real_inner_comm y (quadraticOperator O x)]
  ring

@[simp] theorem quadraticPotential_gradient {d : ℕ} (O : Rotations d) :
    gradient (quadraticPotential O) = quadraticOperator O :=
  gradient_eq (quadraticPotential_hasGradientAt O)

theorem quadraticPotential_admissible {d : ℕ} (O : Rotations d) :
    Admissible (quadraticPotential O) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (contDiff_id.inner ℝ (quadraticOperator O).contDiff).div_const 2
  · simp [quadraticPotential]
  · simp
  · intro x v
    rw [quadraticPotential_gradient, (quadraticOperator O).fderiv]
    exact quadraticOperator_bounds O v

theorem quadratic_firstOrderReply {d : ℕ} (O : Rotations d) (x : Point d) :
    firstOrderReply (quadraticPotential O) x =
      (inner ℝ x (quadraticOperator O x) / 2, quadraticOperator O x) := by
  simp [firstOrderReply, quadraticPotential]

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
