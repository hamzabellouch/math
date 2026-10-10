import OAI.Analysis.Mahler.MatrixHessian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

open Complex MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Mahler

abbrev ComplexEuclidean (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The hypotheses for the isolated-zero mass inequality.
This structure records hypotheses; it does not assert the inequality. -/
structure MassHypotheses (n N m : ℕ) (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ)
    (G : Fin N → MvPolynomial (Fin n) ℂ) : Prop where
  dimension_pos : 1 ≤ n
  degree_pos : 1 ≤ m
  open_domain : IsOpen U
  zero_mem : (0 : ComplexEuclidean n) ∈ U
  holomorphic : ∀ j, DifferentiableOn ℂ (f j) U
  isolated_zero : ∀ z ∈ U, (∀ j, f j z = 0) ↔ z = 0
  homogeneous : ∀ j, (G j).IsHomogeneous m
  leading_nonzero : ∀ z : ComplexEuclidean n, z ≠ 0 →
    ∃ j, MvPolynomial.eval (fun i => z i) (G j) ≠ 0
  taylor_remainder : Asymptotics.IsBigO (𝓝[≠] (0 : ComplexEuclidean n))
    (fun z => (WithLp.toLp 2 (fun j => f j z - MvPolynomial.eval (fun i => z i) (G j)) :
      ComplexEuclidean N)) (fun z => ‖z‖ ^ (m + 1))
  compact_sublevels : ∀ R : ℝ, 0 < R → R < 1 →
    IsCompact (closure (U ∩ {z | tau f z < R})) ∧
      closure (U ∩ {z | tau f z < R}) ⊆ U

/-- The density n! det(tau_{z_k bar z_l}) for the complex Hessian convention. -/
noncomputable def massDensity {n N : ℕ} (f : Fin N → ComplexEuclidean n → ℂ)
    (z : ComplexEuclidean n) : ℝ :=
  (n.factorial : ℝ) * (sourceHessian (energy f) z
    (fun i => EuclideanSpace.single i (1 : ℂ))).det.re

/-- The extended nonnegative integral allows infinite mass.
This definition does not assert its equality to an exterior-form integral. -/
noncomputable def massIntegral {n N : ℕ} (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in U ∩ {z | tau f z < 1}, ENNReal.ofReal (massDensity f z)

def MassBoundTarget : Prop :=
  ∀ (n N m : ℕ) (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) (G : Fin N → MvPolynomial (Fin n) ℂ),
    MassHypotheses n N m U f G →
      ENNReal.ofReal ((Real.pi * (m : ℝ)) ^ n) ≤ massIntegral U f

end Mahler

end OAI
