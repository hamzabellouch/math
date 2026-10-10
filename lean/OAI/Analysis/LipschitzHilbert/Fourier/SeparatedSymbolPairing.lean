import OAI.Analysis.LipschitzHilbert.Fourier.ModulatedInverse

namespace OAI

/-! Fourier separation of the full bilinear form with a measurable
output-dependent direction. The parameter/space interchange follows
from an explicit integrable product majorant. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem separated_symbol_pairing (chi : SchwartzMap ℝ ℝ)
    (hchi : ∀ s, |chi s|≤1) (S : SchwartzMap SymbolSpace ℂ)
    (F : SchwartzMap (ℝ×ℝ) ℂ) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x)
        ∂planeMeasure) =
    ∫ nu : SymbolSpace, ∫ x,
      (chi (U x):ℂ)*(𝓕 S nu*selectorCharacter nu (U x))*
        planarInverse (modulatedFrequency F nu l W theta center) x*conj (g x)
          ∂planeMeasure := by
  let C : ℝ := ∫ omega, ‖F omega‖ ∂planeMeasure
  let phase := fun p : SymbolSpace×(ℝ×ℝ) =>
    (chi (U p.2):ℂ)*selectorCharacter p.1 (U p.2)*
      planarInverse (modulatedFrequency F p.1 l W theta center) p.2
  let H := fun p : SymbolSpace×(ℝ×ℝ) => (𝓕 S p.1*conj (g p.2))*phase p
  have hC : 0≤C := integral_nonneg (fun _ => norm_nonneg _)
  have hphase : Measurable phase := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact Complex.continuous_ofReal.measurable.comp (chi.continuous.measurable.comp
          (hU.comp measurable_snd))
      · have hc : Continuous (fun p : SymbolSpace×ℝ => selectorCharacter p.1 p.2) := by
          unfold selectorCharacter
          fun_prop
        exact hc.measurable.comp (measurable_fst.prodMk (hU.comp measurable_snd))
    · exact (modulated_inverse_joint_continuous F l W theta center).measurable
  have hphaseBound (p : SymbolSpace×(ℝ×ℝ)) : ‖phase p‖≤C := by
    have h₁ : ‖(chi (U p.2):ℂ)‖≤1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hchi (U p.2)
    have h₂ := modulated_inverse_norm_le F p.1 l W theta center p.2
    dsimp only [phase]
    rw [norm_mul,norm_mul,norm_selectorCharacter,mul_one]
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hHm : Measurable H := by
    apply Measurable.mul
    · exact ((𝓕 S : SchwartzMap SymbolSpace ℂ).continuous.measurable.comp measurable_fst).mul
        (Complex.continuous_conj.measurable.comp (hgm.comp measurable_snd))
    · exact hphase
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (((𝓕 S : SchwartzMap SymbolSpace ℂ).integrable.norm.mul_prod hg.norm).mul_const C).mono'
      hHm.aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [H]
    rw [norm_mul,norm_mul,RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hphaseBound p) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hleft (x : ℝ×ℝ) :
      (chi (U x):ℂ)*(∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x) =
        ∫ nu : SymbolSpace, H (nu,x) := by
    rw [separated_symbol_operator S F F.integrable,
      ←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with nu
    dsimp only [H,phase]
    ring
  calc
    _ = ∫ x, (∫ nu : SymbolSpace, H (nu,x)) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ nu : SymbolSpace, ∫ x, H (nu,x) ∂planeMeasure :=
      (integral_integral_swap hH).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with nu
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [H,phase]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
