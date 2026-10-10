import OAI.Analysis.CircleDomains.Sobolev.SobolevScalarCoarea
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace OAI

/-! The coarea integral is finite on each bounded measurable set. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_gradient_integrableOn_bounded
    {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hb : IsBounded E) : IntegrableOn (fun p => ‖V p‖) E := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact hV.norm.integrable (by norm_num)

 theorem sobolev_coarea_ae_finite_levels
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E) :
    ∀ᵐ t ∂volume, (μH[1] : Measure EuclideanPlane) (E ∩ {p | v p = t}) < ∞ := by
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb (fun _ => 1) measurable_const
  simp only [one_mul] at he
  have hi : (∫⁻ p in E, ENNReal.ofReal ‖V p‖) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_norm, ofReal_norm] using
      (local_gradient_integrableOn_bounded hLp hb).hasFiniteIntegral
  have ha := ae_lt_top' hm (he.trans_lt hi).ne
  simpa only [sobolevLevelIntegral, lintegral_one, Measure.restrict_apply_univ] using ha

end CircleDomainRigidity

end

end OAI
