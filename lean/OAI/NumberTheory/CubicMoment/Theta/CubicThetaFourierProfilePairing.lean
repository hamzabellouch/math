import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfileSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionFourierPairing

namespace OAI

/-! Compact Fourier Poincare profiles realize the adjoint cusp observations
as actual global L2 functions. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierProfileSeries_off_cusp (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉cubicThetaQuotientMap '' cubicThetaCuspStrip 2) :
    cubicThetaFourierProfileSeries h p.val W=0 := by
  suffices hz : ∀ r,cubicThetaFourierProfileTerm h r p.val W=0 by
    simp only [cubicThetaFourierProfileSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val≤2
  · exact cubicThetaFourierProfileTerm_zero h r p.val W (hW _ hh)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction (H:=2) (r.completion • p) (by rw [he]; linarith)
  have hq : cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • (r.completion • p))=
      cubicThetaQuotientMap p :=
    (cubicThetaQuotient_covering.map_smul (cubicThetaPrincipalTranslation w)).trans
      (cubicThetaQuotient_covering.map_smul r.completion)
  exact False.elim (hp ⟨_,hw,hq⟩)

def cubicThetaFourierProfileL2 (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaFourierProfileSection h W (fun v hv => hW v (by linarith)))
    (cubicThetaFourierProfileSection_compact h W (fun v hv => hW v (by linarith)))).toLp _

lemma cubicThetaFourierProfilePairing_section (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (hF.toLp _)=
      ∫ p in cubicThetaCuspStrip 2,
        inner ℂ (W p.val.2*cubicThetaHorizontalCharacter h p.val.1) (F.val p) ∂cubicThetaPointMeasure := by
  rw [cubicThetaFourierProfileL2,cubicThetaSectionPairing_L2]
  have he : (∫ q,cubicThetaSectionPairing
      (cubicThetaFourierProfileSection h W (fun v hv => hW v (by linarith))) F q
        ∂cubicThetaQuotientMeasure)=
      ∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip 2,cubicThetaSectionPairing
        (cubicThetaFourierProfileSection h W (fun v hv => hW v (by linarith))) F q
          ∂cubicThetaQuotientMeasure := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz := cubicThetaFourierProfileSeries_off_cusp h W hW (cubicThetaQuotientLift q)
      (by rwa [cubicThetaQuotientLift_map])
    change inner ℂ (cubicThetaFourierProfileSeries h (cubicThetaQuotientLift q).val W) _=0
    rw [hz,inner_zero_left]
  rw [he,cubicThetaInjective_complex_integral (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) _
    (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  dsimp only
  rw [cubicThetaSectionPairing_apply]
  change inner ℂ (cubicThetaFourierProfileSeries h p.val W) _=_
  rw [cubicThetaFourierProfileSeries_high h W (fun v hv => hW v (by linarith))
    (by have hh:=hp.1; change 2<p.val.2 at hh; linarith)]

lemma cubicThetaFourierProfilePairing_finiteEnergy (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaFiniteCuspRestriction F) := by
  change inner ℂ (cubicThetaFourierProfileL2 h W hW) (F.property.2.1.toLp _)=_
  rw [cubicThetaFourierProfilePairing_section h W hW F F.property.2.1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hT hF
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)
  rw [hT,hF]
  rfl

theorem cubicThetaFourierProfilePairing_energy (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner cubicThetaGlobalInclusion.continuous)
      (continuous_const.inner cubicThetaCuspRestriction.continuous)) ?_
  intro F
  rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaCuspRestriction_finiteEnergy]
  exact cubicThetaFourierProfilePairing_finiteEnergy h W hW F

theorem cubicThetaFourierProfileL2_adjoint (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) :
    cubicThetaGlobalInclusion.adjoint (cubicThetaFourierProfileL2 h W hW)=
      cubicThetaCuspRestriction.adjoint (cubicThetaCuspFourierTest h W) := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    cubicThetaFourierProfilePairing_energy]

end CubicFirstMoment

end

end OAI
