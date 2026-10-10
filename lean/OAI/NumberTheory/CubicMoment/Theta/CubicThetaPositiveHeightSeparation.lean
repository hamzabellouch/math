import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightWindowSeparation

namespace OAI

/-! Compact windows separate continuous functions at every positive height. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveHeightWindow_separates {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi (0:ℝ)))
    (hz : ∀ (W : C_c(ℝ,ℂ)) (a d : ℝ),0<a → a≤d →
      (∫ t in Icc a d,star (W t)*F t)=0) {v : ℝ} (hv : 0<v) : F v=0 := by
  let a := v/2
  let d := v+1
  have ha : 0<a := by dsimp [a]; linarith
  have hvi : v∈Ioo a d := by dsimp [a,d]; constructor <;> linarith
  have hc : ContinuousOn F (Ioo a d) := hF.mono (fun t ht => lt_trans ha ht.1)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),t∈Ioo a d → F t=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn measurableSet_Ioo)
    intro g hg hgc hgs
    let W : C_c(ℝ,ℂ) :=
      ⟨⟨fun t => (g t:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
        hgc.comp_left Complex.ofReal_zero⟩
    have he : (∫ t : ℝ,g t • F t)=∫ t in Icc a d,g t • F t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g t=0 := image_eq_zero_of_notMem_tsupport
        (fun hs => ht ⟨(hgs hs).1.le,(hgs hs).2.le⟩)
      rw [hg0,zero_smul]
    rw [he]
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using
        hz W a d ha (le_trans hvi.1.le hvi.2.le)
  have hae' : F=ᵐ[volume.restrict (Ioo a d)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hae] with t ht he
    exact he ht
  exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hc continuousOn_const hvi


end CubicFirstMoment

end

end OAI
