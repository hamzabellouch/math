import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroWindow

namespace OAI

/-! A compact radial Poincaré profile supported above two pairs with the
actual constant cusp observation, including on the completed energy space. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileSeries_off_cusp (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉cubicThetaQuotientMap '' cubicThetaCuspStrip 2) :
    cubicThetaRadialProfileSeries p.val W=0 := by
  suffices hz : ∀ r, cubicThetaRadialProfileTerm r p.val W=0 by
    simp only [cubicThetaRadialProfileSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (hW _ hh)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction (H:=2) (r.completion • p) (by rw [he]; linarith)
  have hq : cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • (r.completion • p))=
      cubicThetaQuotientMap p :=
    (cubicThetaQuotient_covering.map_smul (cubicThetaPrincipalTranslation w)).trans
      (cubicThetaQuotient_covering.map_smul r.completion)
  exact False.elim (hp ⟨_,hw,hq⟩)

def cubicThetaRadialProfileL2 (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith)))
    (cubicThetaRadialProfileSection_compact W (fun v hv => hW v (by linarith)))).toLp _

lemma cubicThetaRadialProfilePairing_section (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (hF.toLp _)=
      ∫ p in cubicThetaCuspStrip 2,
        inner ℂ (W p.val.2) (F.val p) ∂cubicThetaPointMeasure := by
  rw [cubicThetaRadialProfileL2,cubicThetaSectionPairing_L2]
  have he : (∫ q, cubicThetaSectionPairing (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith))) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip 2,
        cubicThetaSectionPairing (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith))) F q
          ∂cubicThetaQuotientMeasure := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz := cubicThetaRadialProfileSeries_off_cusp W hW (cubicThetaQuotientLift q)
      (by rwa [cubicThetaQuotientLift_map])
    change inner ℂ (cubicThetaRadialProfileSeries (cubicThetaQuotientLift q).val W) _=0
    rw [hz,inner_zero_left]
  rw [he,cubicThetaInjective_complex_integral (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) _
    (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  dsimp only
  rw [cubicThetaSectionPairing_apply]
  change inner ℂ (cubicThetaRadialProfileSeries p.val W) _=_
  rw [cubicThetaRadialProfileSeries_high W (fun v hv => hW v (by linarith))
    (by have h:=hp.1; change 2<p.val.2 at h; linarith)]

lemma cubicThetaRadialProfilePairing_finiteEnergy (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaCuspFourierTest 0 (W))
        (cubicThetaFiniteCuspRestriction F) := by
  change inner ℂ (cubicThetaRadialProfileL2 W hW) (F.property.2.1.toLp _)=_
  rw [cubicThetaRadialProfilePairing_section W hW F F.property.2.1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 (W)).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 (W)).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)
  rw [hW,hF]
  simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]

theorem cubicThetaRadialProfilePairing_energy (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaCuspFourierTest 0 (W))
        (cubicThetaCuspRestriction u) := by
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace |
      inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion v)=
        inner ℂ (cubicThetaCuspFourierTest 0 (W))
          (cubicThetaCuspRestriction v)} := isClosed_eq
    (continuous_const.inner cubicThetaGlobalInclusion.continuous)
    (continuous_const.inner cubicThetaCuspRestriction.continuous)
  have hr : range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace |
        inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion v)=
          inner ℂ (cubicThetaCuspFourierTest 0 (W))
            (cubicThetaCuspRestriction v)} := by
    rintro v ⟨F,rfl⟩
    change inner ℂ (cubicThetaRadialProfileL2 W hW)
      (cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F))=_
    rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaCuspRestriction_finiteEnergy]
    exact cubicThetaRadialProfilePairing_finiteEnergy W hW F
  exact (closure_minimal hr hc) (cubicThetaFiniteEnergyEmbedding_dense u)


end CubicFirstMoment

end

end OAI
