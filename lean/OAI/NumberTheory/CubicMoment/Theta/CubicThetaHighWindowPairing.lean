import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroWindow

namespace OAI

/-! The global pairing with the high forcing is exactly the constant
cusp observation, first on actual sections and then on the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHighWindowSeries_off_cusp (s : ℂ) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉cubicThetaQuotientMap '' cubicThetaCuspStrip 2) :
    cubicThetaHighWindowSeries p.val s=0 := by
  suffices hz : ∀ r, cubicThetaHighWindowTerm r p.val s=0 by
    simp only [cubicThetaHighWindowSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s hh)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction (H:=2) (r.completion • p) (by rw [he]; linarith)
  have hq : cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • (r.completion • p))=
      cubicThetaQuotientMap p :=
    (cubicThetaQuotient_covering.map_smul (cubicThetaPrincipalTranslation w)).trans
      (cubicThetaQuotient_covering.map_smul r.completion)
  exact False.elim (hp ⟨_,hw,hq⟩)

lemma cubicThetaInjective_complex_integral {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaQuotient → ℂ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaInjective_map_restrict hS hi]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

def cubicThetaHighWindowL2 (s : ℂ) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaHighWindowSection s)
    (cubicThetaHighWindowSection_compact s)).toLp _

lemma cubicThetaHighWindowPairing_section (s : ℂ) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    inner ℂ (cubicThetaHighWindowL2 s) (hF.toLp _)=
      ∫ p in cubicThetaCuspStrip 2,
        inner ℂ (cubicThetaHighWindowForcing s p.val.2) (F.val p) ∂cubicThetaPointMeasure := by
  rw [cubicThetaHighWindowL2,cubicThetaSectionPairing_L2]
  have he : (∫ q, cubicThetaSectionPairing (cubicThetaHighWindowSection s) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip 2,
        cubicThetaSectionPairing (cubicThetaHighWindowSection s) F q
          ∂cubicThetaQuotientMeasure := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz := cubicThetaHighWindowSeries_off_cusp s (cubicThetaQuotientLift q)
      (by rwa [cubicThetaQuotientLift_map])
    change inner ℂ (cubicThetaHighWindowSeries (cubicThetaQuotientLift q).val s) _=0
    rw [hz,inner_zero_left]
  rw [he,cubicThetaInjective_complex_integral (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) _
    (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  dsimp only
  rw [cubicThetaSectionPairing_apply]
  change inner ℂ (cubicThetaHighWindowSeries p.val s) _=_
  rw [cubicThetaHighWindowSeries_high (by have h:=hp.1; change 2<p.val.2 at h; linarith) s]

lemma cubicThetaHighWindowPairing_finiteEnergy (s : ℂ) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
        (cubicThetaFiniteCuspRestriction F) := by
  change inner ℂ (cubicThetaHighWindowL2 s) (F.property.2.1.toLp _)=_
  rw [cubicThetaHighWindowPairing_section s F F.property.2.1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight s)).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight s)).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)
  rw [hW,hF]
  simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair,cubicThetaHighWindowWeight]

theorem cubicThetaHighWindowPairing_energy (s : ℂ) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
        (cubicThetaCuspRestriction u) := by
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace |
      inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion v)=
        inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
          (cubicThetaCuspRestriction v)} := isClosed_eq
    (continuous_const.inner cubicThetaGlobalInclusion.continuous)
    (continuous_const.inner cubicThetaCuspRestriction.continuous)
  have hr : range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace |
        inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion v)=
          inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
            (cubicThetaCuspRestriction v)} := by
    rintro v ⟨F,rfl⟩
    change inner ℂ (cubicThetaHighWindowL2 s)
      (cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F))=_
    rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaCuspRestriction_finiteEnergy]
    exact cubicThetaHighWindowPairing_finiteEnergy s F
  exact (closure_minimal hr hc) (cubicThetaFiniteEnergyEmbedding_dense u)

theorem cubicThetaHighWindowPairing_residue_zero_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaHighWindowL2 σ)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))=0 := by
  rw [cubicThetaHighWindowPairing_energy]
  exact cubicThetaSpectralResidue_window_zero_closed (cubicThetaHighWindowWeight σ)
    (fun _ hv => cubicThetaHighWindowForcing_low σ hv) hσ hσ2 hne

theorem cubicThetaHighWindowPairing_residue_zero {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaHighWindowL2 σ)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))=0 :=
  cubicThetaHighWindowPairing_residue_zero_closed hσ hσ2.le hne

end CubicFirstMoment

end

end OAI
