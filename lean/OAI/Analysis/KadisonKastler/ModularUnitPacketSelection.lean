import OAI.Analysis.KadisonKastler.ModularPacketSelection

namespace OAI

/-! # Unit-vector form of modular packet separation -/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem exists_short_spectral_unit_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (ξ : H), ‖ξ‖=1 ∧ S.upperCut r ξ=ξ ∧ S.upperCut (r+δ) ξ=0 ∧
      c < (inner ℂ ξ (T ξ)).re := by
  obtain ⟨r,η,hη,hlo,hhi,hgt⟩ := S.exists_short_spectral_vector_gt ψ hψ hinv T hT hc hδ
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let ξ : H := (((‖η‖⁻¹ : ℝ) : ℂ)) • η
  refine ⟨r,ξ,?_,?_,?_,?_⟩
  · change ‖(((‖η‖⁻¹ : ℝ) : ℂ)) • η‖=1
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  · change S.upperCut r ((((‖η‖⁻¹ : ℝ) : ℂ)) • η)=_
    rw [map_smul,hlo]
  · change S.upperCut (r+δ) ((((‖η‖⁻¹ : ℝ) : ℂ)) • η)=0
    rw [map_smul,hhi,smul_zero]
  · have he : (inner ℂ ξ (T ξ)).re=‖η‖⁻¹^2*(inner ℂ η (T η)).re := by
      change (inner ℂ (((‖η‖⁻¹ : ℝ) : ℂ) • η)
        (T (((‖η‖⁻¹ : ℝ) : ℂ) • η))).re=_
      rw [map_smul,inner_smul_left,inner_smul_right]
      change (star ((‖η‖⁻¹ : ℝ) : ℂ)*
        (((‖η‖⁻¹ : ℝ) : ℂ)*inner ℂ η (T η))).re=_
      simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hgt (sq_pos_of_pos (inv_pos.mpr hn))
    have hi : ‖η‖⁻¹^2*‖η‖^2=1 := by rw [← mul_pow,inv_mul_cancel₀ hn.ne']; norm_num
    have heq : ‖η‖⁻¹^2*(c*‖η‖^2)=c := by
      calc
        _ = c*(‖η‖⁻¹^2*‖η‖^2) := by ring
        _ = c := by rw [hi,mul_one]
    rwa [heq] at hm

end ModularSpectralResolution

end

end KadisonKastler

end OAI
