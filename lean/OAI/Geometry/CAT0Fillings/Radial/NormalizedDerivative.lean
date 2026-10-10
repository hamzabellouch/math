import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.ChartMass
import OAI.Geometry.CAT0Fillings.Radial.IntegralDerivative
import OAI.Geometry.CAT0Fillings.Radial.MeasurableBound

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

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)
local instance : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := _root_.borel _
local instance : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
theorem radial_normalized_integral_hasDerivWithinAt_zero
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (μ : Measure (Euc k)) [IsFiniteMeasure μ] (hμ : μ ≪ volume.restrict C.domain) :
    HasDerivWithinAt
      (fun t => ∫ z, C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z / Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∂μ)
      (∫ z, -((k:ℝ)*C.scalar g z+C.scalar (dist o) z *
        (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ
          (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z)))) ∂μ)
      (Ici 0) 0 := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  obtain ⟨G,hG,heG⟩ := (C.scalar_lipschitzOn hL hg).extend_real
  let P (z : Euc k) := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let q : Euc k → MetricRadialParameters (Fin k) := fun z =>
    (P z,((C.scalar g z,C.scalar (dist o) z),
      (differentialRow (fderiv ℝ R z),differentialRow (fderiv ℝ G z))))
  have hPm : Measurable P := by
    have hh : Measurable (fun z i j => P z i j) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm i j
    have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
      BorelSpace.measurable_eq.symm
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) P
    rw [heq]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hGd : Measurable (fun z => differentialRow (fderiv ℝ G z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hq : Measurable q := hPm.prodMk
    ((C.measurable_scalar hg).prodMk (C.measurable_scalar (LipschitzWith.dist_right o)) |>.prodMk
      (hRd.prodMk hGd))
  have hRae := ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR
  have hGae := ae_fderivWithin_eq_fderiv_extension volume C.borel hG heG
  have hdata : ∀ᵐ z ∂volume.restrict C.domain,
      |(q z).2.1.1| ≤ B ∧ |(q z).2.1.2| ≤ B ∧
      (∀ v : Fin k → ℝ, ((q z).2.2.1 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (q z).1.mulVec v)) ∧
      (∀ v : Fin k → ℝ, ((q z).2.2.2 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (q z).1.mulVec v)) := by
    filter_upwards [hp,ae_restrict_mem C.borel,hRae,hGae,
      C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
      C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hRz hGz hRb hGb
    have hP : (P z).PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
    have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ (P z).mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [q,C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩)
    · simpa only [q,C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩)
    · intro v
      change (differentialRow (fderiv ℝ R z) ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (P z).mulVec v)
      rw [hRz] at hRb
      have hh := hRb v
      simp only [NNReal.coe_one,one_pow,one_mul] at hh
      exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
    · intro v
      change (differentialRow (fderiv ℝ G z) ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (P z).mulVec v)
      rw [hGz] at hGb
      exact (hGb v).trans (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hpos : ∀ᵐ z ∂μ, (q z).1.PosDef := by
    filter_upwards [hμ.ae_le hp] with z hz
    exact polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  have hh := integrated_intrinsicRadialJacobian_hasDerivWithinAt_zero μ q hq hB0
    (hμ.ae_le hdata) hpos
  convert hh using 1
  · funext t
    apply integral_congr_ae
    filter_upwards [hμ.ae_le hRae,hμ.ae_le hGae] with z hRz hGz
    simp only [radialJacobian,q,P,hRz,hGz]
  · apply integral_congr_ae
    filter_upwards [hμ.ae_le hRae,hμ.ae_le hGae] with z hRz hGz
    simp only [q,P,hRz,hGz,Fintype.card_fin]
end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)

theorem radial_weighted_integral_hasDerivWithinAt_zero
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    HasDerivWithinAt
      (fun t => ∫ z, |(C.multiplicity z : ℝ)| * C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z ∂volume.restrict C.domain)
      (∫ z, (|(C.multiplicity z : ℝ)| * Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) *
        -((k:ℝ)*C.scalar g z+C.scalar (dist o) z *
        (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ
          (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z))))
        ∂volume.restrict C.domain)
      (Ici 0) 0 := by
  let ν := volume.restrict C.domain
  let ρ : Euc k → ℝ := fun z => |(C.multiplicity z : ℝ)| * Real.sqrt
    (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
  let μ := ν.withDensity (fun z => ENNReal.ofReal (ρ z))
  have hρ0 (z) : 0 ≤ ρ z := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hρ.hasFiniteIntegral
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hh := C.radial_normalized_integral_hasDerivWithinAt_zero p hpm hp o hg μ hμ
  have hchange (f : Euc k → ℝ) : (∫ z, f z ∂μ) = ∫ z, ρ z*f z ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    change (∫ z, (ENNReal.ofReal (ρ z)).toReal • f z ∂ν) = _
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change (ENNReal.ofReal (ρ z)).toReal • f z = ρ z * f z
      rw [ENNReal.toReal_ofReal (hρ0 z),smul_eq_mul]
  convert hh using 1
  · funext t
    rw [hchange]
    apply integral_congr_ae
    filter_upwards [hp] with z hz
    have hs : Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1).det_pos)
    dsimp only [ρ]
    field_simp
  · exact (hchange _).symm
end CAT0Fillings.IntegerChart

end
end

end OAI
