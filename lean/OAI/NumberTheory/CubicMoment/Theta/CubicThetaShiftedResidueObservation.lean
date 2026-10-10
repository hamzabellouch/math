import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRadialMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFrequencyContinuation

namespace OAI

/-! The explicit translated-cusp coefficients are the Fourier observations
of the actual spectral residue, not merely of the initial Eisenstein series. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaShiftedWindow_regularized_germ (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    (hhigh : ∀ p∈K,1<p.val.2) {s : ℂ} (hs : 1<s.re) :
    (fun z => (z-4/3)*cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      =ᶠ[𝓝[≠] s]
    (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z) := by
  have hL : MeromorphicOn
      (fun z => (z-4/3)*cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
      (cubicThetaShiftedWindowObservation_meromorphic _ h W a d hK hz)
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
  rw [cubicThetaShiftedWindowObservation_normalized _ h W ha d hK hSK hhigh hz,
    cubicThetaRegularizedShiftedFrequency_right m n hh hz]
  ring

theorem cubicThetaShiftedWindow_residue_coefficient (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    (hhigh : ∀ p∈K,1<p.val.2) :
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
      (fun z : ℂ => (z-4/3)*cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
        cubicThetaRegularizedShiftedFrequency n h (4/3)*
          cubicThetaShiftedWindowRadialTest h W a d (4/3))) := by
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact (cubicThetaShiftedWindow_regularized_germ m n hh W ha had hK hSK hhigh
      (s:=(4/3:ℂ)) (by norm_num)).symm
  exact tendsto_nhds_unique
    (cubicThetaShiftedWindowObservation_residue _ h W a d hK hSK) ht

theorem cubicThetaShiftedWindow_residue_explicit (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 1<a) (had : a≤d) :
    (∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex
          (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) p.val)
      ∂cubicThetaPointMeasure)=
    cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
      (if (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) then
        9*cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3) else 0)*
      cubicThetaShiftedWindowRadialTest h W a d (4/3) := by
  classical
  obtain ⟨K,hK,hSK,hbound⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  rw [cubicThetaShiftedWindow_residue_coefficient m n hh W (by linarith) had hK hSK
    (fun p hp => ha.trans_le (hbound p hp)),cubicThetaRegularizedShiftedFrequency_pole n hh]

end CubicFirstMoment

end

end OAI
