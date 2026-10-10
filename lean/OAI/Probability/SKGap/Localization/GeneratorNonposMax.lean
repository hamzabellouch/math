import Mathlib
import OAI.Probability.SKGap.Localization.Centered
import OAI.Probability.SKGap.Localization.ExpDrift
import OAI.Probability.SKGap.Localization.BilinearCoefficient

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
namespace SKGapCutoff

lemma generator_nonpos_of_max {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (hx : ∀ y, f y ≤ f x) : generator J f x ≤ 0 := by
  rw [generator_flip]
  apply Finset.sum_nonpos
  intro i _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact flipRate_nonneg J x i
  · exact sub_nonpos.mpr (hx _)

lemma eigen_gradient_nonzero {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (a : Fin (Fintype.card (Spin n))) (ha : 0 < spinEigenvalues J hJ hdiag a) :
    ∃ x, 0 < vectorSquare (fun y i => halfDiff i (scalarEigenfunction J hJ hdiag a) y) x := by
  let f := scalarEigenfunction J hJ hdiag a
  by_contra! h
  have hz (i : Fin n) (x : Spin n) : halfDiff i f x=0 := by
    have hs := (Finset.single_le_sum (fun j _ => sq_nonneg (halfDiff j f x))
      (Finset.mem_univ i)).trans (h x)
    nlinarith [sq_nonneg (halfDiff i f x)]
  have hf (x : Spin n) : f x=0 := by
    have he := congrFun (generator_scalarEigenfunction J hJ hdiag a) x
    have he0 : generator J f x=0 := by simp only [generator,hz,mul_zero,Finset.sum_const_zero]
    change generator J f x = -spinEigenvalues J hJ hdiag a*f x at he
    rw [he0] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr ha.ne')
  have hnorm := scalarEigenfunction_inner_self J hJ hdiag a
  change stationaryInner J f f=1 at hnorm
  simp only [stationaryInner,gibbsExpectation,hf,mul_zero,Finset.sum_const_zero] at hnorm
  norm_num at hnorm

theorem hasGap_of_gradient_square {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0) (C : ℝ)
    (hC : ∀ (p : VectorFields n) x,
      (∑ i, 2*p x i*gradientGenerator J p x i) - generator J (vectorSquare p) x ≤
        -2*C*vectorSquare p x) : HasGap J C := by
  apply hasGap_of_positive_eigenvalues J hJ hdiag C
  intro a ha
  let f := scalarEigenfunction J hJ hdiag a
  let p : VectorFields n := fun x i => halfDiff i f x
  obtain ⟨x,hxpos⟩ := eigen_gradient_nonzero J hJ hdiag a ha
  obtain ⟨y,_,hy⟩ := Finset.exists_max_image Finset.univ (vectorSquare p)
    (Finset.univ_nonempty : (Finset.univ : Finset (Spin n)).Nonempty)
  have hymax : ∀ z, vectorSquare p z ≤ vectorSquare p y := fun z => hy z (Finset.mem_univ z)
  have hyp : 0 < vectorSquare p y := hxpos.trans_le (hymax x)
  have he (z : Spin n) (i : Fin n) : gradientGenerator J p z i =
      -spinEigenvalues J hJ hdiag a*p z i := by
    rw [← halfDiff_generator]
    rw [generator_scalarEigenfunction]
    change halfDiff i (fun x => -spinEigenvalues J hJ hdiag a*f x) z = _
    simp only [halfDiff,p]
    ring
  have hs := hC p y
  simp_rw [he] at hs
  have he' : (∑ i, 2*p y i*(-spinEigenvalues J hJ hdiag a*p y i)) =
      -2*spinEigenvalues J hJ hdiag a*vectorSquare p y := by
    simp only [vectorSquare,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he'] at hs
  have hg := generator_nonpos_of_max J (vectorSquare p) y hymax
  nlinarith

theorem hasGap_of_opNorm {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (C : ℝ) (hC : 0 ≤ C)
    (hJC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ C) :
    HasGap J (1-C-4*C^2-4*Real.exp (8*C)*C^2) := by
  apply hasGap_of_gradient_square J hJ hdiag
  intro p x
  have hs := RandomMatrix.rough_square_of_opNorm J hJ C hC hJC p x
  have hd := vectorDissipation_nonneg J p x
  nlinarith

end SKGapCutoff

end

end OAI
