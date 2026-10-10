import OAI.Analysis.CircleDomains.Selection.ProtrusionTestGeometry
import OAI.Analysis.CircleDomains.Modulus.LocalPlateauPayment

namespace OAI

/-! A genuine marked-end protrusion forces a positive lower bound for the localized norm of
every retained real barrier with the prescribed zero anchor. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

theorem width_le_local_barrier_norm
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0)) (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (l : ℕ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (hone : ∀ x ∈ U ∩ d.source, d.coordinate l x = 1)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) (closedBall T.center T.radius)) :
    T.upper - T.lower ≤ ((Real.sqrt Real.pi + 2) * T.boundRadius) *
      (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
       Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2)) := by
  have hp := E.local_plateau_norm_bound hsch harea hG hε hπ hr hq l hU hqU hone
    T.sourceAnchor T.source_inside hzero T.anchorCenter T.anchorRadius T.anchor_image
    T.compact T.in_component isClosed_closedBall (convex_closedBall T.center T.radius)
    T.in_region T.anchor_region hP hPG hPW T.direction measurableSet_Icc
    T.projection T.model_bound T.region_bound
  simpa only [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr T.width_pos.le)] using hp

def barrierThreshold : ℝ := (T.upper - T.lower) / ((Real.sqrt Real.pi + 2) * T.boundRadius)

theorem barrierThreshold_pos : 0 < T.barrierThreshold := by
  have hR : 0 < T.boundRadius := lt_of_lt_of_le (mul_pos (by norm_num) M.radius_pos) T.model_bound
  exact div_pos (sub_pos.mpr T.width_pos)
    (mul_pos (by positivity) hR)

theorem barrierThreshold_le_norm
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0)) (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (l : ℕ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (hone : ∀ x ∈ U ∩ d.source, d.coordinate l x = 1)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) (closedBall T.center T.radius)) :
    T.barrierThreshold ≤
      Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  have hR : 0 < T.boundRadius := lt_of_lt_of_le (mul_pos (by norm_num) M.radius_pos) T.model_bound
  apply (div_le_iff₀ (mul_pos (by positivity : 0 < Real.sqrt Real.pi + 2) hR)).mpr
  simpa only [mul_comm] using
    T.width_le_local_barrier_norm hsch harea hG hε hπ hr hq l hU hqU hone hzero hP hPG hPW

end CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry

end

end OAI
