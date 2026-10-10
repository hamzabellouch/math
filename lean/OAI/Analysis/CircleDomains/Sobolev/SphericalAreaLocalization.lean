import OAI.Analysis.CircleDomains.Topology.SphereLevels
import OAI.Analysis.CircleDomains.Topology.SmallPhysicalDisks
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def sphericalAreaDensity (z : ℂ) : ℝ := 4 / (1 + ‖z‖ ^ 2) ^ 2

theorem sphericalAreaDensity_pos (z : ℂ) : 0 < sphericalAreaDensity z := by
  unfold sphericalAreaDensity
  positivity

theorem continuous_sphericalAreaDensity : Continuous sphericalAreaDensity := by
  unfold sphericalAreaDensity
  exact continuous_const.div ((continuous_const.add (continuous_norm.pow 2)).pow 2)
    (fun z => by positivity)

def sphericalArea : Measure Sphere :=
  Measure.map ((↑) : ℂ → Sphere)
    (volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z)))

theorem lintegral_sphericalArea (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻x, g x ∂sphericalArea =
      ∫⁻z : ℂ, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  rw [sphericalArea, lintegral_map hg OnePoint.continuous_coe.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (hg.comp OnePoint.continuous_coe.measurable)

theorem planar_energy_on_compact_finite {K : Set ℂ} (hK : IsCompact K)
    (g : ℂ → ℝ≥0∞)
    (henergy : (∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2) < ∞) :
    (∫⁻z in K, g z ^ 2) < ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_sphericalAreaDensity.continuousOn
  let c := ENNReal.ofReal (sphericalAreaDensity z₀)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z₀)).ne'
  have hcle (z : ℂ) (hz : z ∈ K) : c ≤ ENNReal.ofReal (sphericalAreaDensity z) :=
    ENNReal.ofReal_le_ofReal (hmin hz)
  have hbound : c * (∫⁻z in K, g z ^ 2) < ∞ := by
    rw [← lintegral_const_mul' c _ (by exact ENNReal.ofReal_ne_top)]
    apply lt_of_le_of_lt _ henergy
    calc
      (∫⁻z in K, c * g z ^ 2) ≤
          ∫⁻z in K, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 := by
        apply setLIntegral_mono' hK.measurableSet
        intro z hz
        exact mul_le_mul' (hcle z hz) le_rfl
      _ ≤ ∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  by_contra h
  have heq : (∫⁻z in K, g z ^ 2) = ∞ := top_unique (not_lt.mp h)
  simp [heq, ENNReal.mul_top hc] at hbound

theorem planar_energy_quotient_neighborhood_finite
    (π : Sphere → Sphere) (hπ : Continuous π) {O : Set Sphere}
    (hinfty : π OnePoint.infty ∉ closure O)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞ := by
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure O)) :=
    isCompact_finite_preimage (isClosed_closure.preimage hπ) hinfty
  have he := planar_energy_on_compact_finite hK (fun z => g (z : Sphere))
  rw [lintegral_sphericalArea _ (hg.pow_const 2)] at henergy
  exact (lintegral_mono_set (preimage_mono subset_closure)).trans_lt (he henergy)

end CircleDomainRigidity

end

end OAI
