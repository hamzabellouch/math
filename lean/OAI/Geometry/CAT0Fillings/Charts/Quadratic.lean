import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Charts.LinearMass
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Geometry.Determinant

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Set Metric Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]
theorem exists_chart_matrix_determinant_bound {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ P : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, Measurable (fun x => P x i j)) ∧
      (∀ᵐ x ∂volume.restrict s, (P x).PosDef) ∧
      (∀ᵐ x ∂volume.restrict s, Real.sqrt (P x).det ≤ (K : ℝ)^n) ∧
      ∀ π : Fin n → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
        ∀ᵐ x ∂volume.restrict s,
          |(Matrix.of fun i j =>
            fderivWithin ℝ (scalarOn f (π i)) s x (EuclideanSpace.single j 1)).det| ≤
              Real.sqrt (P x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨p,hpm,hpLip,hae⟩ := exists_hilbertian_chart_differential volume hs hsf hf hJ hQ
  have hzero : ∀ᵐ x ∂volume.restrict s, ∀ v, p x v = 0 ↔ v = 0 := by
    filter_upwards [hae] with x hx v
    constructor
    · intro hv
      have hn := hx.2.2 v
      rw [hv,mul_zero] at hn
      exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg v))
    · rintro rfl
      exact map_zero (p x)
  refine ⟨fun x => polarizationMatrix (p x) b,measurable_polarizationMatrix p b hpm,?_,?_,?_⟩
  · filter_upwards [hae,hzero] with x hx hz
    exact polarizationMatrix_posDef b (p x) hz hx.2.1
  · filter_upwards [hae,hzero] with x hx hz
    apply sqrt_det_le_pow_of_quadratic_bound _
      (polarizationMatrix_posDef b (p x) hz hx.2.1).posSemidef K.coe_nonneg
    intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hrepr : b.repr w = v := by ext j; simp [b,w]
    have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
      simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
    rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
    simpa only [dist_zero_right,map_zero,Real.norm_eq_abs, abs_of_nonneg (apply_nonneg (p x) w)] using (hpLip x).dist_le_mul w 0
  intro π hπ
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := hae.mono fun x hx => hx.1
  have hrows : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ p x v := by
    rw [eventually_all]
    intro i
    simpa only [NNReal.coe_one,one_mul] using ae_scalarOn_derivative_bound volume hs hf hdiff (hπ i)
  filter_upwards [hae,hzero,hrows] with x hx hz hrow
  apply abs_det_le_sqrt_det_of_posDef _ _ (polarizationMatrix_posDef b (p x) hz hx.2.1)
  intro i v
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by
    ext j
    simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
  convert hrow i w using 1
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = w := by
    convert b.sum_repr w using 1
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.of_apply, dotProduct, mul_comm]
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

theorem exists_quadratic_majorant (hX : IsCAT0 X) :
    ∃ P : Euc k → Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, Measurable (fun z => P z i j)) ∧
      (∀ᵐ z ∂volume.restrict C.domain, (P z).PosDef) ∧
      Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
        (volume.restrict C.domain) ∧
      IsFiniteMeasure (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      Controls C.action (C.majorantMeasure (fun z => Real.sqrt (P z).det)) := by
  obtain ⟨K,L,hK,hL⟩ := C.bilipschitz
  obtain ⟨P,hPm,hP,hJ,hdet⟩ := MetricDifferentiation.exists_chart_matrix_determinant_bound
    C.borel C.bounded.measure_lt_top.ne hK hL
    (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d))
  have hJm : Measurable (fun z => Real.sqrt (P z).det) := by
    apply Measurable.sqrt
    simp only [Matrix.det_apply']
    fun_prop
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
      (volume.restrict C.domain) := by
    apply (C.integrable.abs.mul_const ((K : ℝ)^k)).mono'
      (C.integrable.abs.aestronglyMeasurable.mul hJm.aestronglyMeasurable)
    filter_upwards [hJ] with z hz
    change ‖|(C.multiplicity z : ℝ)| * Real.sqrt (P z).det‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  refine ⟨P,hPm,hP,hρ,?_,?_⟩
  · exact densityPush_finite _ _ hρ
  · apply C.majorant_controls hρ (Eventually.of_forall fun z => Real.sqrt_nonneg _)
    intro π hπ
    exact hdet π hπ

end IntegerChart
end CAT0Fillings

end

end OAI
