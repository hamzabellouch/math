import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactIntegralRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedIncoming
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelSection

namespace OAI

/-! Bounded observations of the actual translated-cusp Eisenstein family.
Their residues are the already constructed arithmetic theta model, sampled
at the same Mobius transform. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaIncoming_shifted_zero (b : Eisenstein) {p : ℂ×ℝ}
    (hp : 1<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s=0 := by
  have hz : ∀ r : CubicThetaBottomRow, cubicThetaIncomingTerm r
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s=0 := by
    intro r
    unfold cubicThetaIncomingTerm
    rw [cubicThetaBottomRow_height_shiftedInverted r b (by linarith),
      cubicThetaCuspCutoff_zero (cubicThetaInvertedRow_height_le_one _ hp),zero_mul]
  simp only [cubicThetaIncomingEisenstein,hz,tsum_zero]

lemma cubicThetaRemainder_shifted (b : Eisenstein) {p : ℂ×ℝ}
    (hp : 1<p.2) (s : ℂ) :
    cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s=
      cubicThetaEisenstein
        ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s := by
  rw [cubicThetaArithmeticRemainder,cubicThetaIncoming_shifted_zero b hp,sub_zero,
    cubicThetaMobius_shiftedInversion b (by linarith)]

def cubicThetaCompactShiftedFamily (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) (s : ℂ) : Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
    (cubicThetaResidueScale • cubicThetaForcedResolvent s)

lemma cubicThetaCompactShiftedFamily_meromorphic (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaCompactShiftedFamily b hK) s := by
  apply cubicThetaMeromorphic_clm (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK)
  exact (cubicThetaForcedResolvent_meromorphic hs).const_smul cubicThetaResidueScale

lemma cubicThetaCompactShiftedFamily_right (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) (hhigh : ∀ p∈K,1<p.val.2) {s : ℂ} (hs : 3<s.re) :
    cubicThetaCompactShiftedFamily b hK s=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => cubicThetaResidueScale*cubicThetaEisenstein
        ((cubicThetaInversion 1 p.val).1+b,(cubicThetaInversion 1 p.val).2) s) := by
  have hF := cubicThetaCompactIntegralRestriction_section (cubicThetaShiftedInversion b) hK
    (cubicThetaArithmeticSection s (by linarith)) (cubicThetaArithmeticSection_memLp hs)
  have hscalar := Lp.coeFn_smul cubicThetaResidueScale
    (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
      ((cubicThetaArithmeticSection_memLp hs).toLp _))
  rw [cubicThetaCompactShiftedFamily,map_smul,←cubicThetaArithmeticL2_eq_forcedResolvent hs]
  dsimp only [cubicThetaArithmeticL2]
  filter_upwards [hscalar,hF,ae_restrict_mem hK.measurableSet] with p hp hFp hKp
  rw [hp]
  change cubicThetaResidueScale*_= _
  rw [hFp]
  change cubicThetaResidueScale*cubicThetaArithmeticRemainder
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val) s=_
  rw [cubicThetaRemainder_shifted b (hhigh p hKp)]

lemma cubicThetaCompactShiftedFamily_residue (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) :
    Tendsto (fun s : ℂ => (s-4/3) • cubicThetaCompactShiftedFamily b hK s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue))) := by
  let L := cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
  have ht := (L.continuous.tendsto _).comp
    ((continuous_const_smul cubicThetaResidueScale).tendsto _ |>.comp
      (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)))
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at ht
  change Tendsto (fun s : ℂ => L (cubicThetaResidueScale • ((s-4/3) • cubicThetaForcedResolvent s)))
    (𝓝[≠] (4/3:ℂ))
    (𝓝 (L (cubicThetaResidueScale • cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) at ht
  rw [cubicThetaNormalizedArithmeticResidue,map_smul]
  apply ht.congr'
  filter_upwards with s
  change L (cubicThetaResidueScale • ((s-4/3) • cubicThetaForcedResolvent s))=
    (s-4/3) • L (cubicThetaResidueScale • cubicThetaForcedResolvent s)
  rw [smul_comm cubicThetaResidueScale (s-4/3),map_smul]

lemma cubicThetaCompactShiftedResidue_model (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) :
    cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure.restrict K]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
          (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
  have hmodel := (measurePreserving_smul (cubicThetaShiftedInversion b)
    cubicThetaPointMeasure).quasiMeasurePreserving.ae cubicThetaArithmeticModel_global_ae
  filter_upwards [cubicThetaCompactIntegralRestriction_coe (cubicThetaShiftedInversion b) hK
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue),
    ae_restrict_of_ae hmodel] with p hp hmp
  exact hp.trans hmp

end CubicFirstMoment

end

end OAI
