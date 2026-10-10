import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergySimplePole
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalMeromorphic

namespace OAI

/-! Transfer of the simple energy pole to the Eisenstein parameter.
The derivative factor is explicit and nonzero on the real interval (1,2). -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSpectralParameter_gap (a b : ℂ) :
    cubicThetaGlobalSpectralParameter a-cubicThetaGlobalSpectralParameter b=
      (b-a)*(b+a-2) := by
  unfold cubicThetaGlobalSpectralParameter
  ring

lemma cubicThetaSpectralParameter_punctured {σ : ℝ} (hσ : 1<σ) :
    Tendsto cubicThetaGlobalSpectralParameter (𝓝[≠] (σ:ℂ))
      (𝓝[≠] (cubicThetaGlobalSpectralParameter (σ:ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact ((continuous_const.sub (continuous_id.mul (continuous_id.sub continuous_const))).tendsto _).mono_left
      nhdsWithin_le_nhds
  · have hnear : ∀ᶠ s : ℂ in 𝓝 (σ:ℂ), 1<s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hσ)
    filter_upwards [nhdsWithin_le_nhds hnear,self_mem_nhdsWithin] with s hs hne
    change cubicThetaGlobalSpectralParameter s≠cubicThetaGlobalSpectralParameter (σ:ℂ)
    intro he
    have hprod : (s-(σ:ℂ))*(s+(σ:ℂ)-2)=0 := by
      rw [← cubicThetaSpectralParameter_gap,he,sub_self]
    have hsum : s+(σ:ℂ)-2≠0 := by
      intro hz
      have hre := congrArg Complex.re hz
      simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hre
      norm_num at hre
      linarith
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum))

lemma cubicThetaRealSpectralParameter_range {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    0<1-σ*(σ-2) ∧ 1-σ*(σ-2)<2 := by
  constructor
  · nlinarith [mul_neg_of_pos_of_neg (by linarith : 0<σ) (by linarith : σ-2<0)]
  · nlinarith [sq_pos_of_pos (by linarith : 0<σ-1)]

lemma cubicThetaRealSpectralParameter_closedRange {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    0<1-σ*(σ-2) ∧ 1-σ*(σ-2)<2 := by
  constructor
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤σ) (by linarith : σ-2≤0)]
  · nlinarith [sq_pos_of_pos (by linarith : 0<σ-1)]

private lemma spectral_rescale {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b : ℂ) (hb : b+a-2≠0) (u : E) :
    -(b+a-2)⁻¹ • ((cubicThetaGlobalSpectralParameter b-cubicThetaGlobalSpectralParameter a) • u)=
      (b-a) • u := by
  rw [smul_smul,cubicThetaSpectralParameter_gap]
  have he : -(b+a-2)⁻¹*((a-b)*(a+b-2))=b-a := by
    have hba : a+b-2=b+a-2 := by ring
    rw [hba]
    field_simp [hb]
    ring
  rw [he]

private lemma rescale_associative {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b : ℂ) (u : E) : a • (b • u)=(a*b) • u := smul_smul a b u

theorem cubicThetaSpectralEnergyInverse_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)))
      (𝓝[≠] (σ:ℂ))
      (𝓝 ((cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)))) := by
  let _ : NormedRing (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let _ : NormedAlgebra ℂ (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  have hr := cubicThetaRealSpectralParameter_closedRange hσ hσ2
  have hz : ((1-σ*(σ-2):ℝ):ℂ)=cubicThetaGlobalSpectralParameter (σ:ℂ) := by
    simp only [cubicThetaGlobalSpectralParameter,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hp₀ := cubicThetaEnergyInverse_residue hr.1 hr.2
  rw [hz] at hp₀
  have hp := hp₀.comp (cubicThetaSpectralParameter_punctured hσ)
  have hden : ((σ:ℂ)+(σ:ℂ)-2)≠0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hc : ContinuousAt (fun s : ℂ => -(s+(σ:ℂ)-2)⁻¹) (σ:ℂ) :=
    ((continuousAt_id.add continuousAt_const).sub continuousAt_const).inv₀ hden |>.neg
  have h := (hc.tendsto.mono_left nhdsWithin_le_nhds).smul hp
  have hnear : ∀ᶠ s : ℂ in 𝓝 (σ:ℂ), s+(σ:ℂ)-2≠0 :=
    ((continuousAt_id.add continuousAt_const).sub continuousAt_const).eventually_ne hden
  have he : (fun s : ℂ => -(s+(σ:ℂ)-2)⁻¹ •
      ((cubicThetaGlobalSpectralParameter s-cubicThetaGlobalSpectralParameter (σ:ℂ)) •
        Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s))))=ᶠ[𝓝[≠] (σ:ℂ)]
      (fun s : ℂ => (s-(σ:ℂ)) •
        Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s))) := by
    filter_upwards [nhdsWithin_le_nhds hnear] with s hs
    exact spectral_rescale (σ:ℂ) s hs _
  have hcval : -((σ:ℂ)+(σ:ℂ)-2)⁻¹ •
      (-cubicThetaGlobalSpectralParameter (σ:ℂ) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)))=
      (cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)) := by
    have hc : -((σ:ℂ)+(σ:ℂ)-2)⁻¹*(-cubicThetaGlobalSpectralParameter (σ:ℂ))=
        cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ) := by
      have he : ((2*σ-2:ℝ):ℂ)=(σ:ℂ)+(σ:ℂ)-2 := by push_cast; ring
      rw [he,div_eq_mul_inv]
      ring
    exact (rescale_associative _ _ _).trans (congrArg (fun c : ℂ => c •
      cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))) hc)
  rw [hcval] at h
  exact h.congr' he

theorem cubicThetaSpectralEnergyInverse_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)))
      (𝓝[≠] (σ:ℂ))
      (𝓝 ((cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)))) :=
  cubicThetaSpectralEnergyInverse_residue_closed hσ hσ2.le

end CubicFirstMoment

end

end OAI
