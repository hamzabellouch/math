import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X]
lemma det_rows_eq_zero_of_seminorm_kernel {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hL : ∀ i, ∃ K : ℝ, ∀ v, |L i v| ≤ K*p v)
    (hker : ¬ ∀ v, p v = 0 → v = 0) :
    Matrix.det (fun i j => L i (EuclideanSpace.single j 1)) = 0 := by
  classical
  push Not at hker
  obtain ⟨v,hpv,hv⟩ := hker
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun j => v j,?_,?_⟩
  · intro h
    apply hv
    ext j
    simpa using congrFun h j
  · ext i
    obtain ⟨K,hK⟩ := hL i
    have hLv : L i v = 0 := by
      apply abs_nonpos_iff.mp
      simpa only [hpv,mul_zero] using hK v
    have hsum : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = v := by
      simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    have hli := congrArg (L i) hsum
    rw [_root_.map_sum] at hli
    simp only [map_smul,smul_eq_mul] at hli
    change ∑ j, L i (EuclideanSpace.single j 1) * v j = 0
    simpa only [mul_comm,hLv] using hli

theorem ae_scalarOn_det_eq_zero_of_degenerate {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f)
    {p : EuclideanSpace ℝ (Fin n) → Seminorm ℝ (EuclideanSpace ℝ (Fin n))}
    (hd : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    (π : Fin n → X → ℝ) (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict s, (¬ ∀ v, p x v = 0 → v = 0) →
      Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
        (EuclideanSpace.single j 1)) = 0 := by
  choose J hJ using hπ
  have hb : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ (J i : ℝ)*p x v := by
    rw [eventually_all]
    intro i
    exact ae_scalarOn_derivative_bound volume hs hf hd (hJ i)
  filter_upwards [hb] with x hx hker
  exact det_rows_eq_zero_of_seminorm_kernel (p x) _ (fun i => ⟨J i,hx i⟩) hker

end CAT0Fillings.MetricDifferentiation

end

end OAI
