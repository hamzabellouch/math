import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartGradientProjectionSmooth

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma metric_mul_chartGradientProjection (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (i j : CoordIndex E) :
    ∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)*
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)/
      localGradientPair g u u p y := by
  let α := fun k => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E k)
  have he : (metricCoefficients g p y) *ᵥ
      ((metricCoefficients g p y)⁻¹ *ᵥ α) = α := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne'),Matrix.one_mulVec]
  have hei := congrFun he i
  simp only [Matrix.mulVec,dotProduct] at hei
  simp only [chartGradientProjection,chartGradientField,coordinateFlux]
  simp_rw [mul_div_assoc,←mul_assoc]
  dsimp [α] at hei
  rw [←Finset.sum_mul,hei]

theorem conductivity_metric_realization_projection (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ ĝ : SmoothMetric E M,
      (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
      (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
      (∀ (p : M) (y : E), y ∈ (chartAt E p).target →
        coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0 →
        ∀ i j : CoordIndex E,
        metricCoefficients ĝ p y i j-metricCoefficients g p y i j =
          (Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y))-1)*
            metricCoefficients g p y i j +
          (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-
            Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y)))*
            ∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
  obtain ⟨a,b,ha,hb,ha0,hab0,hdet,hflux,hext⟩ :=
    determinant_correction_coefficients g u hu d q hd hq hd0 hq0 hsupp
  let ĝ := differentialMetric g u hu a b ha hb ha0 hab0
  have hdiag (x : M) : a x+b x*coordinateGradientPair g u u x=d x/q x := by
    have hh := (div_eq_iff (hab0 x).ne').mp (hflux x)
    apply (eq_div_iff (hq0 x).ne').mpr
    linarith
  have hsqrt (x : M) : a x=Real.sqrt (d x*q x) := by
    have hh := hdet x
    rw [hdiag x] at hh
    have hqz := (hq0 x).ne'
    have he : a x^2=d x*q x := by
      have hh' := congrArg (fun r : ℝ => r*q x) hh
      field_simp [hqz] at hh'
      apply (mul_right_cancel₀ (hd0 x).ne')
      nlinarith [hh']
    rw [←he,Real.sqrt_sq (ha0 x).le]
  refine ⟨ĝ,differentialMetric_laplacian_three hn g u hu a b d q ha hb ha0 hab0 hd0 hdet hflux,?_,?_⟩
  · intro x hdx hqx v w
    obtain ⟨hax,hbx⟩ := hext x hdx hqx
    change a x*g.inner x v w+b x*inner ℝ (scalarDifferential u x v) (scalarDifferential u x w)=_
    rw [hax,hbx]; simp
  · intro p y hy hF i j
    have hc := differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy
    have hbF : b ((chartAt E p).symm y) =
        (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-a ((chartAt E p).symm y))/
          coordinateGradientPair g u u ((chartAt E p).symm y) := by
      apply (eq_div_iff hF).mpr
      linarith [hdiag ((chartAt E p).symm y)]
    change metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y i j-_=_
    rw [hc,metric_mul_chartGradientProjection g u p hy i j,
      localGradientPair_eq_global hu g p hy]
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
    rw [hbF,hsqrt]
    ring

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conductivity_metric_realization_complete (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ ĝ : SmoothMetric E M,
      (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
      (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
      (∀ x, d x=q x^3 → ∀ v w, ĝ.inner x v w=q x^2*g.inner x v w) ∧
      (∀ (p : M) (y : E), y ∈ (chartAt E p).target →
        coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0 →
        ∀ i j : CoordIndex E,
        metricCoefficients ĝ p y i j-metricCoefficients g p y i j =
          (Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y))-1)*
            metricCoefficients g p y i j +
          (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-
            Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y)))*
            ∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
  obtain ⟨a,b,ha,hb,ha0,hab0,hdet,hflux,hext⟩ :=
    determinant_correction_coefficients g u hu d q hd hq hd0 hq0 hsupp
  let ĝ := differentialMetric g u hu a b ha hb ha0 hab0
  have hdiag (x : M) : a x+b x*coordinateGradientPair g u u x=d x/q x := by
    have hh := (div_eq_iff (hab0 x).ne').mp (hflux x)
    apply (eq_div_iff (hq0 x).ne').mpr
    linarith
  have hsqrt (x : M) : a x=Real.sqrt (d x*q x) := by
    have hh := hdet x
    rw [hdiag x] at hh
    have hqz := (hq0 x).ne'
    have he : a x^2=d x*q x := by
      have hh' := congrArg (fun r : ℝ => r*q x) hh
      field_simp [hqz] at hh'
      apply (mul_right_cancel₀ (hd0 x).ne')
      nlinarith [hh']
    rw [←he,Real.sqrt_sq (ha0 x).le]
  refine ⟨ĝ,differentialMetric_laplacian_three hn g u hu a b d q ha hb ha0 hab0 hd0 hdet hflux,?_,?_,?_⟩
  · intro x hdx hqx v w
    obtain ⟨hax,hbx⟩ := hext x hdx hqx
    change a x*g.inner x v w+b x*inner ℝ (scalarDifferential u x v) (scalarDifferential u x w)=_
    rw [hax,hbx]; simp
  · intro x heq v w
    have haq : a x=q x^2 := by
      rw [hsqrt x,heq,show q x^3*q x=(q x^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
    have hz : b x*coordinateGradientPair g u u x=0 := by
      have hh := hdiag x
      rw [haq,heq] at hh
      have hdiv : q x^3/q x=q x^2 := by field_simp
      rw [hdiv] at hh
      linarith
    change a x*g.inner x v w+b x*inner ℝ (scalarDifferential u x v) (scalarDifferential u x w)=_
    rw [haq]
    rcases mul_eq_zero.mp hz with hbz | hFz
    · rw [hbz]; simp
    · have hv : scalarDifferential u x v=0 := by
        have hj := scalarDifferential_dual_bound hu g x v
        rw [hFz,zero_mul] at hj
        nlinarith [sq_nonneg (scalarDifferential u x v)]
      rw [hv]; simp
  · intro p y hy hF i j
    have hc := differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy
    have hbF : b ((chartAt E p).symm y) =
        (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-a ((chartAt E p).symm y))/
          coordinateGradientPair g u u ((chartAt E p).symm y) := by
      apply (eq_div_iff hF).mpr
      linarith [hdiag ((chartAt E p).symm y)]
    change metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y i j-_=_
    rw [hc,metric_mul_chartGradientProjection g u p hy i j,
      localGradientPair_eq_global hu g p hy]
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
    rw [hbF,hsqrt]
    ring


end YauCounterexamples
end

end OAI
