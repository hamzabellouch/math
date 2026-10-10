import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Scalar
import OAI.Geometry.CAT0Fillings.Radial.MeasurableBound
import OAI.Geometry.CAT0Fillings.Radial.Integrability
import OAI.Geometry.CAT0Fillings.Radial.NormalizedDerivative

namespace OAI

section
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
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ}
theorem uniform_chart_radialJacobian_slope
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (C : IntegerChart X k) (p : Euc k → Seminorm ℝ (Euc k)),
      (∀ᵐ z ∂volume.restrict C.domain,
        (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
          C.domain C.param (p z) ⟨z,hz⟩) ∧
        (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
        (∀ v, p z v = 0 ↔ v = 0)) →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ᵐ z ∂volume.restrict C.domain,
        |C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z - Real.sqrt (polarizationMatrix (p z)
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det| ≤ A*t*Real.sqrt
            (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  obtain ⟨A,hA,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := Fin k) B hB0
  refine ⟨A,hA,?_⟩
  intro C p hp t ht
  filter_upwards [hp,ae_restrict_mem C.borel,
    C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
    C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hR hG
  let P := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hP : P.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ P.mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
  have hα : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    have hh := hR v
    simp only [NNReal.coe_one,one_pow,one_mul] at hh
    exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
  have hγ : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    exact (hG v).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hh := hbound P hP (C.scalar g z) (C.scalar (dist o) z)
    (by simpa only [C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩))
    (by simpa only [C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩))
    _ _ hα hγ t ht
  have hpos : 0 < Real.sqrt P.det := Real.sqrt_pos.2 hP.det_pos
  change |C.radialJacobian (fun z => polarizationMatrix (p z)
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z / Real.sqrt P.det-1| ≤ A*t at hh
  have he (r s : ℝ) (hs : s ≠ 0) : r/s-1 = (r-s)/s := by field_simp
  rw [he _ _ hpos.ne',abs_div,abs_of_pos hpos] at hh
  exact (div_le_iff₀ hpos).1 hh
end CAT0Fillings

namespace CAT0Fillings
open Set Filter
open scoped Topology

theorem hasDerivWithinAt_tsum_of_uniform_right_slope
    {ι : Type*} (F : ι → ℝ → ℝ) (d b : ι → ℝ)
    (h0 : Summable (fun i => F i 0)) (hb : Summable b)
    (hd : ∀ i, HasDerivWithinAt (F i) (d i) (Ici 0) 0)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ i, |F i t-F i 0| ≤ t*b i) :
    Summable d ∧ HasDerivWithinAt (fun t => ∑' i, F i t) (∑' i, d i) (Ici 0) 0 := by
  have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
  have hlim (i) : Tendsto (fun t => (F i t-F i 0)/t) (𝓝[>] (0:ℝ)) (𝓝 (d i)) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (hd i)
    change Tendsto (fun t => slope (F i) 0 t) _ _ at h
    simpa only [hs,slope_def_field,sub_zero] using h
  have hevent : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, ‖(F i t-F i 0)/t‖ ≤ b i := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    intro i
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<t from ht)]
    apply (div_le_iff₀ ht).2
    simpa only [mul_comm] using hbound t ⟨ht.le,ht1.le⟩ i
  have hdi (i) : ‖d i‖ ≤ b i :=
    le_of_tendsto (hlim i |>.norm) (hevent.mono fun t ht => ht i)
  refine ⟨hb.of_norm_bounded hdi,?_⟩
  have ht := tendsto_tsum_of_dominated_convergence hb hlim hevent
  rw [hasDerivWithinAt_iff_tendsto_slope,hs]
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  have hdiff : Summable (fun i => F i t-F i 0) :=
    (hb.mul_left t).of_norm_bounded fun i => by
      simpa only [Real.norm_eq_abs] using hbound t ⟨ht.le,ht1.le⟩ i
  have hFt : Summable (fun i => F i t) := by
    convert hdiff.add h0 using 1
    funext i
    ring
  rw [slope_def_field,sub_zero,tsum_div_const,hFt.tsum_sub h0]
end CAT0Fillings
namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ}

theorem countable_chart_radial_first_variation
    (C : ℕ → IntegerChart X k) (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hpm : ∀ i v, Measurable (fun z => p i z v))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0))
    (hρ : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict (C i).domain))
    (hsum : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
      ∂volume.restrict (C i).domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    let d : ℕ → ℝ := fun i => ∫ z,
      (|((C i).multiplicity z : ℝ)| * Real.sqrt
        (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) *
      -((k:ℝ)*(C i).scalar g z+(C i).scalar (dist o) z *
        (differentialRow (fderivWithin ℝ ((C i).scalar (dist o)) (C i).domain z) ⬝ᵥ
          (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ ((C i).scalar g) (C i).domain z))))
      ∂volume.restrict (C i).domain
    Summable d ∧ HasDerivWithinAt
      (fun t => ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| * (C i).radialJacobian
        (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z ∂volume.restrict (C i).domain) (∑' i, d i) (Ici 0) 0 := by
  dsimp only
  let P (i : ℕ) (z : Euc k) :=
    polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let ρ (i : ℕ) (z : Euc k) := |((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det
  let F (i : ℕ) (t : ℝ) := ∫ z, |((C i).multiplicity z : ℝ)| *
    (C i).radialJacobian (P i) o g t z ∂volume.restrict (C i).domain
  have hF0 (i) : F i 0 = ∫ z, ρ i z ∂volume.restrict (C i).domain := by
    simp only [F,ρ,IntegerChart.radialJacobian,metricSpatialRadialForm]
    simp
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨A,_,hbound⟩ := uniform_chart_radialJacobian_slope (k := k) o hg hB hK hgb hrb
  apply hasDerivWithinAt_tsum_of_uniform_right_slope F _
    (fun i => A*(∫ z, ρ i z ∂volume.restrict (C i).domain))
    (by simpa only [hF0,ρ,P] using hsum) (hsum.mul_left A)
  · intro i
    exact (C i).radial_weighted_integral_hasDerivWithinAt_zero
      (p i) (hpm i) (hp i) (hρ i) o hg
  · intro t ht i
    have hIt := (C i).integrable_radialJacobian (p i) (hpm i) (hp i) (hρ i)
      o hg hB hK hgb hrb ht
    rw [hF0]
    change |(∫ z, |((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z
      ∂volume.restrict (C i).domain) - (∫ z, ρ i z ∂volume.restrict (C i).domain)| ≤ _
    rw [←integral_sub hIt (hρ i)]
    calc
      _ ≤ ∫ z, |(|((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z - ρ i z)|
          ∂volume.restrict (C i).domain := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (fun z => |((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z - ρ i z)
      _ ≤ ∫ z, (t*A)*ρ i z ∂volume.restrict (C i).domain := by
        apply integral_mono_ae (hIt.sub (hρ i)).abs ((hρ i).const_mul (t*A))
        filter_upwards [hbound (C i) (p i) (hp i) t ht] with z hz
        change |(|((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z -
          |((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det)| ≤
          t*A*(|((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det)
        rw [←mul_sub,abs_mul,abs_abs]
        calc
          _ ≤ |((C i).multiplicity z : ℝ)| * (A*t*Real.sqrt (P i z).det) :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg _)
          _ = (t*A)*(|((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det) := by ring
      _ = _ := by rw [integral_const_mul]; ring
end CAT0Fillings
end
end

end OAI
