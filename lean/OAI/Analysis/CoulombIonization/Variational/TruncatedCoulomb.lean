import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def truncatedCoulomb (R : ℝ) : Space → ℝ := (ball 0 R).indicator (fun x => 1/‖x‖)

def unitCoulombIntegral : ℝ := ∫ x : Space, truncatedCoulomb 1 x

lemma truncatedCoulomb_nonneg (R : ℝ) (x : Space) : 0 ≤ truncatedCoulomb R x := by
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

lemma unitCoulombIntegral_nonneg : 0 ≤ unitCoulombIntegral :=
  integral_nonneg (truncatedCoulomb_nonneg 1)

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) := by
  have hi := (CoulombAnalysis.nuclear_memLp R).integrable (Fact.out : (1:ENNReal) ≤ 5/2)
  exact (show IntegrableOn (fun x : Space => 1/‖x‖) (ball 0 R) by
    simpa only [CoulombAnalysis.ballMeasure,IntegrableOn,one_div] using hi).integrable_indicator measurableSet_ball

lemma truncatedCoulomb_scaling {R : ℝ} (hR : 0 < R) (x : Space) :
    truncatedCoulomb R x = R⁻¹ * truncatedCoulomb 1 (R⁻¹ • x) := by
  have hmem : R⁻¹ • x ∈ ball (0 : Space) 1 ↔ x ∈ ball (0 : Space) R := by
    simp only [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    rw [inv_mul_lt_iff₀ hR]
    simp only [mul_one]
  by_cases hx : x ∈ ball (0 : Space) R
  · simp only [truncatedCoulomb,indicator_of_mem hx,indicator_of_mem (hmem.mpr hx),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),one_div,mul_inv_rev,inv_inv]
    field_simp
  · simp only [truncatedCoulomb,indicator_of_notMem hx,indicator_of_notMem (mt hmem.mp hx),mul_zero]

lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 < R) :
    (∫ x : Space, truncatedCoulomb R x) = R^2*unitCoulombIntegral := by
  simp_rw [truncatedCoulomb_scaling hR]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg _ _ hR.le]
  simp only [Space,finrank_euclideanSpace_fin,smul_eq_mul]
  unfold unitCoulombIntegral
  field_simp

lemma radialPacketBase_bound (x : Space) : ‖radialPacketBase x‖ ≤ 1 := by
  rw [radialPacketBase,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

def packetDensityConstant : ℝ := (Fintype.card (Spins 1) : ℝ) / formMass (smoothForm radialPacketSeed)

lemma packetDensityConstant_pos : 0 < packetDensityConstant :=
  div_pos (Nat.cast_pos.mpr Fintype.card_pos) radialPacketSeed_mass_pos

lemma packetDensity_bound (y x : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity y r x ≤ packetDensityConstant/r^3 := by
  rw [packetDensity_formula,inv_pow,Real.sq_sqrt (radialScaledRaw_mass_pos hr).le,
    radialScaledRaw_mass r hr]
  have hdim : Module.finrank ℝ (Configuration 1) = 3 := by
    change Module.finrank ℝ (Fin 1 → Space) = 3
    rw [Module.finrank_pi_fintype]
    simp only [Space,finrank_euclideanSpace_fin,Fin.sum_univ_one]
  rw [hdim]
  calc
    _ ≤ (Fintype.card (Spins 1) : ℝ) * (r^3*formMass (smoothForm radialPacketSeed))⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [radialPacketSeed_mass_pos])
      have hb := radialPacketBase_bound (r⁻¹ • (x-y))
      nlinarith [norm_nonneg (radialPacketBase (r⁻¹ • (x-y)))]
    _ = _ := by unfold packetDensityConstant; ring

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
