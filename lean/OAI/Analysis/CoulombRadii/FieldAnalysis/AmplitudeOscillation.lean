import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.ScaledOscillation

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem poisson_amplitude_negative_oscillation {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ,0 < C ∧ ∀ (F σ : Position → ℝ) (y : Position) (a lam : ℝ),0 < a → 0 < lam →
      ContinuousOn F (Metric.ball y (3*a)) →
      HasWeakLaplacian F (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x,0 ≤ σ x) →
      (∀ x∈Metric.closedBall y (3*a),σ x ≤ lam*(A/a^6)) →
      (∀ x∈Metric.closedBall y (2*a),F x ≤ lam*(M/a^4)) →
      F y ≤ (∫ x,F x*Coulomb.ballCloud y (2*a) 1 x) →
      ∀ z∈Metric.closedBall y a,
        ‖F z-F y‖ ≤ C*(‖z-y‖/a)*(lam/a^4+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_scaled_negative_oscillation hA hM
  refine ⟨C,hC,?_⟩
  intro F σ y a lam ha hlam hF hLap hi hp hb hcap hmean z hz
  let G := fun x => lam⁻¹*F x
  let τ := fun x => lam⁻¹*σ x
  have hGL : HasWeakLaplacian G (Metric.ball y (2*a)) (fun x => 4*Real.pi*τ x) := by
    convert hLap.const_mul lam⁻¹ using 1
    funext point
    dsimp [G,τ]
    ring
  have hτA (x) (hx : x∈Metric.closedBall y (3*a)) : τ x ≤ A/a^6 := by
    dsimp [τ]
    have hh := mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.mpr hlam.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hlam.ne',one_mul] using hh
  have hGM (x) (hx : x∈Metric.closedBall y (2*a)) : G x ≤ M/a^4 := by
    dsimp [G]
    have hh := mul_le_mul_of_nonneg_left (hcap x hx) (inv_nonneg.mpr hlam.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hlam.ne',one_mul] using hh
  have hGmean : G y ≤ ∫ x,G x*Coulomb.ballCloud y (2*a) 1 x := by
    dsimp [G]
    simp_rw [mul_assoc,integral_const_mul]
    exact mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr hlam.le)
  have HH := H G τ y a ha (hF.const_mul lam⁻¹) hGL (hi.const_mul _)
    (fun x => mul_nonneg (inv_nonneg.mpr hlam.le) (hp x)) hτA hGM hGmean z hz
  have hm : max (-(lam⁻¹*F y)) 0=lam⁻¹*max (-F y) 0 := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hlam.le)]
    simp only [mul_zero,mul_neg]
  change ‖lam⁻¹*F z-lam⁻¹*F y‖ ≤ C*(‖z-y‖/a)*((a^4)⁻¹+max (-(lam⁻¹*F y)) 0) at HH
  rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam),hm] at HH
  have he : C*(‖z-y‖/a)*((a^4)⁻¹+lam⁻¹*max (-F y) 0)=
      lam⁻¹*(C*(‖z-y‖/a)*(lam/a^4+max (-F y) 0)) := by
    field_simp [hlam.ne']
  rw [he] at HH
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hlam)).mp HH
end NeutralAtom
end

end

end OAI
