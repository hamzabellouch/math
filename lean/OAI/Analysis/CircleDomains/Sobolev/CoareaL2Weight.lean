import OAI.Analysis.CircleDomains.Sobolev.CoareaL2Errors

namespace OAI

/-! A locally square-integrable weight is integrable on almost every
bounded scalar Sobolev level. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_L2_weight_finite
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : EuclideanPlane → ℝ} (hq : Measurable q) (hL : MemLp q 2 (volume.restrict E)) :
    ∀ᵐ t ∂volume, sobolevLevelIntegral E v (fun p => ENNReal.ofReal ‖q p‖) t < ∞ := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb
    (fun p => ENNReal.ofReal ‖q p‖) (ENNReal.measurable_ofReal.comp hq.norm)
  have hbound := lintegral_norm_mul_le_L2 hL hV.norm
  simp only [norm_norm] at hbound
  apply ae_lt_top' hm
  rw [he]
  exact (hbound.trans_lt ENNReal.ofReal_lt_top).ne

end CircleDomainRigidity

end

end OAI
