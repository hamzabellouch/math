import OAI.NumberTheory.CubicMoment.Estimates.UniformHeightMellin
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! The two actual Poisson signs, with the Fourier Jacobian retained,
for a translation-uniform arbitrary height mass. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem normMellin_signed_height_uniform (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B T u : ℝ),
      0 ≤ B → 0 < T → (∀ t, ‖G t‖ ≤ E) →
      (∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          ((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ D*B := by
  obtain ⟨D,hD,hmean⟩ := arithmeticMellin_signed_height_uniform M hM V hV hV' q
  refine ⟨D/(2*Real.pi),by positivity,?_⟩
  intro ρ hρ G hG E B T u hB hT hbound havg
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  let f := fun s => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖
  let P := fun t => ∫ s : ℝ, ‖A s‖*G (t+u+s)
  let Q := fun t => ∫ s : ℝ, ‖A (-s)‖*G (t+u+s)
  have hi : Integrable f := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have he (t : ℝ) : (∫ s : ℝ, f s*((G (t+u+2*Real.pi*s)+
      G (t+u-(2*Real.pi*s)))/2)) = (4*Real.pi)⁻¹*(P t+Q t) := by
    have hp : Integrable (fun s : ℝ => f s*G (t+u+2*Real.pi*s)) :=
      hi.mul_bdd (hG.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => hbound _))
    have hn : Integrable (fun s : ℝ => f s*G (t+u-(2*Real.pi*s))) :=
      hi.mul_bdd (hG.comp (continuous_const.sub (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => hbound _))
    have hs := integral_scaled_signed_mass f (fun s => G (t+u+s))
      (by positivity : 0 < 2*Real.pi) hp (by simpa only [sub_eq_add_neg] using hn)
    calc
      _ = ((∫ s : ℝ, f (s/(2*Real.pi))*G (t+u+s))+
          (∫ s : ℝ, f (-(s/(2*Real.pi)))*G (t+u+s)))/(2*(2*Real.pi)) := by
        simpa only [sub_eq_add_neg] using hs
      _ = _ := by
        dsimp [P,Q,A,f,arithmeticMellinCoefficient]
        simp only [neg_div]
        ring
  have hac : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hai : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hpc : Continuous P := continuous_height_convolution hac.norm hai.norm hG hbound u
  have hqc : Continuous Q := continuous_height_convolution (hac.comp continuous_neg).norm
    hai.norm.comp_neg hG hbound u
  have hp := hmean ρ hρ G hG E B T u 1 (Or.inl rfl) hB hT hbound havg
  have hq := hmean ρ hρ G hG E B T u (-1) (Or.inr rfl) hB hT hbound havg
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hq
  change (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
    f s*((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ _
  simp_rw [he]
  rw [dyadicHeightMean_const_mul,dyadicHeightMean_add hpc hqc]
  calc
    _ = ((1+ρ)^q*dyadicHeightMean P T+(1+ρ)^q*dyadicHeightMean Q T)/(4*Real.pi) := by ring
    _ ≤ (D*B+D*B)/(4*Real.pi) := div_le_div_of_nonneg_right (add_le_add hp hq) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
