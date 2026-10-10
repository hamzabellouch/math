import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFullFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFrequencyContinuation

namespace OAI

/-! The full corrected compact observations identify the actual translated
residue at every positive height, including the low-height incoming term. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaShiftedFullWindow_regularized_germ (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    {s : ℂ} (hs : 1<s.re) :
    (fun z => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      =ᶠ[𝓝[≠] s]
    (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z) := by
  have hL : MeromorphicOn
      (fun z => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
      (cubicThetaShiftedFullObservation_meromorphic _ h W ha d hK hz)
  have hR : MeromorphicOn (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const cubicThetaResidueScale z).mul
      ((MeromorphicAt.const (Real.pi:ℂ) z).div
        (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt)).mul
      (cubicThetaRegularizedShiftedFrequency_analytic n hh z hz).meromorphicAt).mul
      ((cubicThetaShiftedWindowRadial_entire hh W ha had).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaShiftedFullObservation_normalized _ h W ha d hK hSK hz,
    cubicThetaRegularizedShiftedFrequency_right m n hh hz]
  ring

theorem cubicThetaShiftedFullWindow_residue_coefficient (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    :
    (∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex
          (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) p.val)
      ∂cubicThetaPointMeasure)=
    cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
      cubicThetaRegularizedShiftedFrequency n h (4/3)*
        cubicThetaShiftedWindowRadialTest h W a d (4/3) := by
  have hc : ContinuousAt (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z)
      (4/3:ℂ) :=
    ((continuousAt_const.mul (continuousAt_const.div
      (cubicThetaGamma_analytic_right (by norm_num : (0:ℝ)<(4/3:ℂ).re)).continuousAt
        (Complex.Gamma_ne_zero_of_re_pos (by norm_num)))).mul
      (cubicThetaRegularizedShiftedFrequency_analytic n hh (4/3) (by norm_num)).continuousAt).mul
      ((cubicThetaShiftedWindowRadial_entire hh W ha had).analyticAt (4/3)).continuousAt
  have ht : Tendsto
      (fun z : ℂ => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
        cubicThetaRegularizedShiftedFrequency n h (4/3)*
          cubicThetaShiftedWindowRadialTest h W a d (4/3))) := by
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact (cubicThetaShiftedFullWindow_regularized_germ m n hh W ha had hK hSK
      (s:=(4/3:ℂ)) (by norm_num)).symm
  exact tendsto_nhds_unique
    (cubicThetaShiftedFullObservation_residue _ h W ha d hK hSK) ht


end CubicFirstMoment

end

end OAI
