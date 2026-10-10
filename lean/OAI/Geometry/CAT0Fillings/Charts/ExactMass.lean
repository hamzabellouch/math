import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Extensions
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertPartition
import OAI.Geometry.CAT0Fillings.Charts.HilbertMass

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

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_mass_measure_le (hX : IsCAT0 X)
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2)) :
    C.majorantMeasure (fun z => Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) ≤ ν := by
  obtain ⟨A,B,hA,hB⟩ := C.bilipschitz
  apply measure_le_of_nearIsometry_factors k
  intro ε hε hε1
  let L : ℝ≥0 := ⟨1+ε,by linarith⟩
  let K : ℝ≥0 := ⟨(1-ε)⁻¹, inv_nonneg.mpr (by linarith)⟩
  have hcoeff : ENNReal.ofReal (((1+ε)/(1-ε))^k) = ((L*K)^k : ℝ≥0) := by
    rw [←ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hcoeff]
  change _ ≤ ((L*K)^k) • ν
  obtain ⟨q,t,ht,hts,hdisj,hnull,_,hq,hnear⟩ :=
    MetricDifferentiation.exists_hilbertian_nearIsometric_chart_partition volume
      C.borel C.bounded.measure_lt_top.ne hA hB
      (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d)) hε
  apply densityPush_le_of_partition C.measurable_paramExtended _ ht hts hdisj hnull
    (fun i => C.measurableSet_paramExtended_image (ht i) (hts i))
  · intro x hx y hy hxy
    exact congrArg (fun z : C.domain => (z : Euc k)) (hB.injective
      (show C.param ⟨x,hx⟩ = C.param ⟨y,hy⟩ from by
        simpa only [paramExtended,dite_eq_left hx,dite_eq_left hy] using hxy))
  intro i
  by_cases hi : (t i).Nonempty
  · have hq0 : ∀ v, q i v = 0 ↔ v = 0 := by
      intro v
      constructor
      · intro hv
        have hh := (hq i hi).2 v
        rw [hv,mul_zero] at hh
        exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
      · rintro rfl
        exact map_zero _
    apply C.hilbert_piece_mass_le hC hν (ht i) (hts i) p (q i) hq0 (hq i hi).1
      (hp.filter_mono (ae_mono (Measure.restrict_mono (hts i) le_rfl))) K L
    intro y hy z hz
    have hh := hnear i ⟨y,hts i hy⟩ hy ⟨z,hts i hz⟩ hz
    refine ⟨?_,hh.2⟩
    change q i (y-z) ≤ (1-ε)⁻¹ * _
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    simpa only [mul_comm] using hh.1
  · have he : t i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp only [he,Measure.restrict_empty,densityPush,withDensity_zero_left,Measure.map_zero,
      image_empty,le_refl]

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Set Metric Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

lemma chart_matrix_determinant_bound {n : ℕ}
    {s : Set (Euc n)} (hs : MeasurableSet s) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (p : Euc n → Seminorm ℝ (Euc n))
    (hpm : ∀ v, Measurable (fun x => p x v))
    (hpLip : ∀ x, LipschitzWith K (p x))
    (hae : ∀ᵐ x ∂volume.restrict s,
      (∀ hx : x ∈ s, HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
      (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
      (∀ v, ‖v‖ ≤ (J : ℝ)*p x v)) :
    let P := fun x => polarizationMatrix (p x) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (∀ i j, Measurable (fun x => P x i j)) ∧
    (∀ᵐ x ∂volume.restrict s, (P x).PosDef) ∧
    (∀ᵐ x ∂volume.restrict s, Real.sqrt (P x).det ≤ (K : ℝ)^n) ∧
    ∀ π : Fin n → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ x ∂volume.restrict s,
        |(Matrix.of fun i j =>
          fderivWithin ℝ (scalarOn f (π i)) s x (EuclideanSpace.single j 1)).det| ≤
              Real.sqrt (P x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hzero : ∀ᵐ x ∂volume.restrict s, ∀ v, p x v = 0 ↔ v = 0 := by
    filter_upwards [hae] with x hx v
    constructor
    · intro hv
      have hn := hx.2.2 v
      rw [hv,mul_zero] at hn
      exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg v))
    · rintro rfl
      exact map_zero (p x)
  refine ⟨measurable_polarizationMatrix p b hpm,?_,?_,?_⟩
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
open MeasureTheory Set Filter

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

theorem exists_exact_quadratic_mass (hX : IsCAT0 X) (hC : IsMetricCurrent C.action) :
    ∃ P : Euc k → Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, Measurable (fun z => P z i j)) ∧
      (∀ᵐ z ∂volume.restrict C.domain, (P z).PosDef) ∧
      Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
        (volume.restrict C.domain) ∧
      IsFiniteMeasure (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      Controls C.action (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      (∀ (ν : Measure X), IsFiniteMeasure ν → Controls C.action ν →
        C.majorantMeasure (fun z => Real.sqrt (P z).det) ≤ ν) ∧
      ∃ p : Euc k → Seminorm ℝ (Euc k),
        P = (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) ∧
        (∀ v, Measurable (fun z => p z v)) ∧
        ∀ᵐ z ∂volume.restrict C.domain,
          (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
            C.domain C.param (p z) ⟨z,hz⟩) ∧
          (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
          (∀ v, p z v = 0 ↔ v = 0) := by
  obtain ⟨K,L,hK,hL⟩ := C.bilipschitz
  obtain ⟨p,hpm,hpLip,hae⟩ := MetricDifferentiation.exists_hilbertian_chart_differential
    volume C.borel C.bounded.measure_lt_top.ne hK hL
    (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d))
  let P := fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  obtain ⟨hPm,hP,hJ,hdet⟩ := MetricDifferentiation.chart_matrix_determinant_bound
    C.borel hK p hpm hpLip hae
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
  refine ⟨P,hPm,hP,hρ,densityPush_finite _ _ hρ,?_,?_,p,rfl,hpm,?_⟩
  · apply C.majorant_controls hρ (Eventually.of_forall fun z => Real.sqrt_nonneg _)
    exact hdet
  · intro ν hνfin hν
    let := hνfin
    apply C.hilbert_mass_measure_le hX hC hν p
    filter_upwards [hae] with z hz
    refine ⟨hz.1,?_,hz.2.1⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _
  · filter_upwards [hae] with z hz
    refine ⟨hz.1,hz.2.1,?_⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _

end IntegerChart
end CAT0Fillings

end

end OAI
