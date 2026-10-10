import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.HilbertCharts
import OAI.Geometry.IntegralFillings.Differentiation.LocalBounds
import OAI.Geometry.IntegralFillings.Charts.MeasurePartition
import OAI.Geometry.IntegralFillings.Charts.LinearMass

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

namespace SharpIntegralFillings
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (p : Euc k → Seminorm ℝ (Euc k)) (q : Seminorm ℝ (Euc k))
    (hq : ∀ v, q v = 0 ↔ v = 0)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    (hp : ∀ᵐ z ∂volume.restrict t,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2))
    (K L : ℝ≥0)
    (hnear : ∀ y (hy : y ∈ t) z (hz : z ∈ t),
      q (y-z) ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ∧
      dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ≤ (L : ℝ)*q (y-z)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      ≤ (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix q b
  let Jq := Real.sqrt Q.det
  have hQ : Q.PosDef := polarizationMatrix_posDef b q hq hqpara
  let ℓ : Fin k → Euc k →L[ℝ] ℝ := fun i => matrixRowFunctional (CFC.sqrt Q) i
  have hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y-ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) := by
    intro i y hy z hz
    rw [←map_sub]
    apply (abs_matrixRow_sqrt_le Q hQ.posSemidef i (y-z)).trans
    simpa only [Q,b,sqrt_polarization_quadratic q hq hqpara,WithLp.toLp_ofLp] using
      (hnear y hy z hz).1
  have hm : (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)) = CFC.sqrt Q := by
    ext i j
    simp only [ℓ,Matrix.of_apply,matrixRowFunctional_single]
  have hdet : |(CFC.sqrt Q).det| = Jq := by
    rw [show (CFC.sqrt Q).det = Real.sqrt Q.det by simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hpiece : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| * Jq) ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
    simpa only [hm,hdet] using C.linear_piece_mass_le hC hν ht hts ℓ K hrow
  have hJ : ∀ᵐ z ∂volume.restrict t,
      Real.sqrt (polarizationMatrix (p z) b).det ≤ (L : ℝ)^k * Jq := by
    filter_upwards [hp,ae_restrict_mem ht,Besicovitch.ae_tendsto_measure_inter_div volume t]
      with z hz hzt hzd
    apply sqrt_det_polarization_le (p z) q hz.2.1 hq hz.2.2 hqpara L.coe_nonneg
    apply (hz.1 (hts hzt)).seminorm_le_on_piece volume hts hzd
    intro y hy
    exact (hnear y hy z hzt).2
  calc
    _ ≤ densityPush (volume.restrict t) C.paramExtended
        (fun z => ((L^k : ℝ≥0) : ℝ) * (|(C.multiplicity z : ℝ)| * Jq)) := by
      apply densityPush_mono_ae C.measurable_paramExtended
      filter_upwards [hJ] with z hz
      have hh := mul_le_mul_of_nonneg_left hz (abs_nonneg (C.multiplicity z : ℝ))
      simpa only [NNReal.coe_pow,mul_left_comm] using hh
    _ = (L^k) • densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)| * Jq) := densityPush_const_mul _ _ _ _
    _ ≤ (L^k) • (((K^k) • ν).restrict (C.paramExtended '' t)) := by
      exact smul_le_smul_left (L^k) hpiece
    _ = (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
      rw [Measure.restrict_smul,smul_smul,←mul_pow,←Measure.restrict_smul]

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma measure_le_of_nearIsometry_factors {β : Type*} [MeasurableSpace β]
    {μ ν : Measure β} [IsFiniteMeasure ν] (k : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      μ ≤ ENNReal.ofReal (((1+ε)/(1-ε))^k) • ν) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k))
      (𝓝[>] 0) (𝓝 1) := by
    have hd : ContinuousAt (fun ε : ℝ => ((1+ε)/(1-ε))^k) 0 := by
      fun_prop (disch := norm_num)
    have hh := ENNReal.continuous_ofReal.continuousAt.comp (x := 0) hd
    simpa only [Function.comp_def,add_zero,sub_zero,div_one,one_pow,ENNReal.ofReal_one] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k)*ν s)
      (𝓝[>] 0) (𝓝 (ν s)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr (measure_ne_top ν s))
  apply ge_of_tendsto hv
  have hε0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hε0,hε1] with ε hε hε'
  simpa only [Measure.smul_apply,smul_eq_mul] using h ε hε hε' s

end SharpIntegralFillings

end

end OAI
