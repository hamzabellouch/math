import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusSlices
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspGreen

namespace OAI

/-! The actual Fourier coefficient map embeds the mean-zero cusp slices
isometrically into the radial mode space used by the compact Green operator. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev CubicThetaAllCuspModes := lp (fun _ : Eisenstein => CubicThetaRadialL2) 2

def cubicThetaCuspFourierVector (F : CubicThetaCuspSlices) : CubicThetaAllCuspModes :=
  ⟨fun h => cubicThetaSliceCoefficient h F, memℓp_gen (by
    simpa using cubicThetaSlices_coefficients_summable F)⟩

lemma cubicThetaCuspFourierVector_norm (F : CubicThetaCuspSlices) :
    ‖cubicThetaCuspFourierVector F‖=‖F‖ := by
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (cubicThetaCuspFourierVector F)
  have he' : ‖cubicThetaCuspFourierVector F‖^2=‖F‖^2 := by
    simpa [cubicThetaCuspFourierVector,cubicThetaSlices_parseval] using he
  nlinarith [_root_.norm_nonneg F,_root_.norm_nonneg (cubicThetaCuspFourierVector F)]

def cubicThetaCuspFourierTransform : CubicThetaCuspSlices →ₗᵢ[ℂ] CubicThetaAllCuspModes where
  toFun := cubicThetaCuspFourierVector
  map_add' F G := by
    apply lp.ext
    funext h
    exact (cubicThetaSliceCoefficient h).map_add F G
  map_smul' c F := by
    apply lp.ext
    funext h
    exact (cubicThetaSliceCoefficient h).map_smul c F
  norm_map' := cubicThetaCuspFourierVector_norm

def cubicThetaMeanZeroSlices : Submodule ℂ CubicThetaCuspSlices :=
  (cubicThetaSliceCoefficient 0).ker

instance cubicThetaMeanZeroSlices_complete : CompleteSpace cubicThetaMeanZeroSlices :=
  (cubicThetaSliceCoefficient 0).isComplete_ker.completeSpace_coe

lemma cubicThetaMeanZeroSlices_zero (F : cubicThetaMeanZeroSlices) :
    cubicThetaSliceCoefficient 0 F.val=0 := F.property

lemma cubicThetaMeanZeroSlices_parseval (F : cubicThetaMeanZeroSlices) :
    (∑' h : CubicThetaNonzeroFrequency, ‖cubicThetaSliceCoefficient h.val F.val‖^2)=‖F‖^2 := by
  have hs : Function.support (fun h : Eisenstein => ‖cubicThetaSliceCoefficient h F.val‖^2) ⊆
      {h | h≠0} := by
    intro h hh hz
    subst h
    have hh' : ‖cubicThetaSliceCoefficient 0 F.val‖^2≠0 := hh
    rw [cubicThetaMeanZeroSlices_zero,_root_.norm_zero] at hh'
    norm_num at hh'
  have he := tsum_subtype_eq_of_support_subset hs
  change (∑' h : {h : Eisenstein | h≠0}, ‖cubicThetaSliceCoefficient h.val F.val‖^2)=‖F.val‖^2
  exact he.trans (cubicThetaSlices_parseval F.val)

def cubicThetaMeanZeroFourierVector (F : cubicThetaMeanZeroSlices) : CubicThetaCuspModes :=
  ⟨fun h => cubicThetaSliceCoefficient h.val F.val, memℓp_gen (by
    have he := (cubicThetaSlices_coefficients_summable F.val).subtype {h : Eisenstein | h≠0}
    change Summable (fun i : CubicThetaNonzeroFrequency => ‖cubicThetaSliceCoefficient i.val F.val‖^2) at he
    simpa using he)⟩

lemma cubicThetaMeanZeroFourierVector_norm (F : cubicThetaMeanZeroSlices) :
    ‖cubicThetaMeanZeroFourierVector F‖=‖F‖ := by
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (cubicThetaMeanZeroFourierVector F)
  have he' : ‖cubicThetaMeanZeroFourierVector F‖^2=‖F‖^2 := by
    simpa [cubicThetaMeanZeroFourierVector,cubicThetaMeanZeroSlices_parseval] using he
  nlinarith [_root_.norm_nonneg F,_root_.norm_nonneg (cubicThetaMeanZeroFourierVector F)]

def cubicThetaMeanZeroFourierTransform : cubicThetaMeanZeroSlices →ₗᵢ[ℂ] CubicThetaCuspModes where
  toFun := cubicThetaMeanZeroFourierVector
  map_add' F G := by
    apply lp.ext
    funext h
    exact (cubicThetaSliceCoefficient h.val).map_add F.val G.val
  map_smul' c F := by
    apply lp.ext
    funext h
    exact (cubicThetaSliceCoefficient h.val).map_smul c F.val
  norm_map' := cubicThetaMeanZeroFourierVector_norm

end CubicFirstMoment

end

end OAI
