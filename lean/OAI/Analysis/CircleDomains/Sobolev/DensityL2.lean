import OAI.Analysis.CircleDomains.Sobolev.PotentialRectangleACL
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The real representative of a finite-energy density is locally L² in
the physical planar chart, including densities that are infinite on a null set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem memLp_two_toReal_of_lintegral_sq_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) (hfinite : (∫⁻x, g x ^ 2 ∂μ) ≠ ∞) :
    MemLp (fun x => (g x).toReal) 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.ennreal_toReal.aestronglyMeasurable).2
  simpa only [ENNReal.toReal_pow] using
    integrable_toReal_of_lintegral_ne_top (hg.pow_const 2).aemeasurable hfinite

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem physical_density_memLp_rectangle
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (a b c d : ℝ) :
    MemLp (fun p : ℝ × ℝ => (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal) 2
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
  let K := closedComplexRectangle a b c d
  have hK : IsCompact K := isCompact_closedComplexRectangle a b c d
  have hgf : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  have hfin : (∫⁻z in K, g (z : Sphere) ^ 2) < ∞ := by
    apply planar_energy_on_compact_finite hK
    rwa [← lintegral_sphericalArea _ (hg.pow_const 2)]
  have hL : MemLp (fun z : ℂ => (g (z : Sphere)).toReal) 2 (volume.restrict K) :=
    memLp_two_toReal_of_lintegral_sq_ne_top _ hgf hfin.ne
  have hI : MemLp (K.indicator (fun z : ℂ => (g (z : Sphere)).toReal)) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).2 hL
  have hP := hI.comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)
  refine MemLp.ae_eq ?_ (hP.restrict (Icc a b ×ˢ Icc c d))
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  exact indicator_of_mem (mk_mem_closedComplexRectangle hp.1 hp.2) _

end CircleDomainRigidity

end

end OAI
