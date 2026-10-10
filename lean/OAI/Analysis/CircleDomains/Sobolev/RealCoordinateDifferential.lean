import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate
import OAI.Analysis.CircleDomains.Sobolev.PlanarDifferentialEnergy

namespace OAI

/-! The actual quotient pullback of a constructed real coordinate has
the smoothness and differential energy used in the path-law estimates.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem PhysicalRealCoordinate.complex_differential
    {d : PathCodeData X Sphere} {π : Sphere → X}
    (Q : PhysicalRealCoordinate d π) (hG : IsOpen d.physicalDomain) :
    ContDiffOn ℝ 1 (fun z : ℂ => Q.quotient (π (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) ∧
    (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) < ∞ := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  let e := Complex.equivRealProdCLM
  let v := Q.physical ∘ e
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hOc : O = e ⁻¹' FiniteTransfer.realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔
      (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hD : IsOpen (FiniteTransfer.realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp e.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (FiniteTransfer.realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by simp)
  have hv : ContDiffOn ℝ 1 v O := by
    rw [hOc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have heq : ∀ z ∈ O, Q.quotient (π (z : Sphere)) = v z :=
    fun z hz => (Q.pullback z hz).symm
  refine ⟨hv.congr heq, ?_⟩
  have henergy : (∫⁻ z in O, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2)) < ∞ := by
    rw [hOc]
    exact complex_chart_differential_energy_finite hD hs Q.physical_energy
  have hderiv (z : ℂ) (hz : z ∈ O) :
      fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z = fderiv ℝ v z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hO.mem_nhds hz] with w hw
    exact heq w hw
  have hi : (∫⁻ z in O, ENNReal.ofReal
      ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) =
      ∫⁻ z in O, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) := by
    apply setLIntegral_congr_fun hO.measurableSet
    intro z hz
    change ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2 =
      ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2)
    rw [hderiv z hz, ENNReal.ofReal_pow (norm_nonneg _)]
  exact hi ▸ henergy

theorem quotientPlaneRepresentative_zero_near_infinity
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (w : EuclideanPlane → ℝ) {K : Set EuclideanPlane} (hK : IsCompact K)
    (hzero : ∀ x ∉ K, w x = 0) :
    (∃ L : Set ℂ, IsCompact L ∧ ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain →
      z ∉ L → quotientPlaneRepresentative d w (π (z : Sphere)) = 0) ∧
    (OnePoint.infty ∈ d.physicalDomain → quotientPlaneRepresentative d w (π OnePoint.infty) = 0) := by
  constructor
  · refine ⟨complexPlaneCoordinates '' K, hK.image complexPlaneCoordinates.continuous, ?_⟩
    intro z hz hn
    rw [← he ⟨(z : Sphere), hz⟩, quotientPlaneRepresentative_on_domain,
      sphereFromPlaneFunction_coe]
    apply hzero
    intro hm
    exact hn ⟨complexPlaneCoordinates.symm z, hm, complexPlaneCoordinates.apply_symm_apply z⟩
  · intro hi
    rw [← he ⟨OnePoint.infty, hi⟩, quotientPlaneRepresentative_on_domain]
    simp only [sphereFromPlaneFunction, ite_true]

end CircleDomainRigidity

end

end OAI
