import OAI.NumberTheory.CubicMoment.Transform.MetaplecticEulerFactor
import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletBounds

namespace OAI

/-! Uniform control of the inverse completion factor on every closed
half-plane strictly inside `Re(s)>1/2`. This follows from the actual
absolutely convergent ideal Möbius inverse. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticCompletionEuler_inverse_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Eisenstein, r ≠ 0 → ∀ s : ℂ,
      1/2+δ ≤ s.re → ‖(metaplecticCompletionEuler r s)⁻¹‖ ≤ C := by
  let C := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(1+3*δ))
  have hsum : Summable (fun ν : EisensteinIdealExponent =>
      idealExponentNorm ν^(-(1+3*δ))) := summable_ideal_norm_rpow (by linarith)
  refine ⟨C,tsum_nonneg (fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _),?_⟩
  intro r hr s hs
  let χ := residueIdealChar (3*r) (1 : MulChar (Residues (3*r)) ℂ)
  have hq : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hχ : ∀ ν, ‖χ ν‖ ≤ 1 := residueIdealChar_norm_le_one hq _
  have hχ0 : χ 0 = 1 := by simp [χ,residueIdealChar,idealExponentGenerator]
  have hχadd : ∀ ν κ, χ (ν+κ) = χ ν*χ κ := residueIdealChar_add _ _
  have hre : 1 < (3*s-(1/2:ℂ)).re := by simp; linarith
  let J := normDirichletSeries
    (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν)
      idealExponentNorm (3*s-1/2)
  have hJ : J*metaplecticCompletionEuler r s = 1 := by
    rw [metaplecticCompletionEuler,primaryCoprimeZeta_eq_ideal hr]
    exact idealDirichlet_moebius_mul χ hχ hχ0 hχadd hre
  have he : J = (metaplecticCompletionEuler r s)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ (metaplecticCompletionEuler_ne_zero hr (by linarith))).mp hJ
  rw [←he]
  have hpoint (ν : EisensteinIdealExponent) :
      ‖(((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν)*
        (idealExponentNorm ν:ℂ)^(-(3*s-1/2))‖ ≤ idealExponentNorm ν^(-(1+3*δ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν)]
    have hexp : (-(3*s-(1/2:ℂ))).re ≤ -(1+3*δ) := by simp; linarith
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)
      (idealMoebius_character_norm χ hχ ν)).trans
      (Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) hexp)
  have habs := hsum.of_nonneg_of_le (fun _ => _root_.norm_nonneg _) hpoint
  exact (norm_tsum_le_tsum_norm habs).trans (Summable.tsum_le_tsum hpoint habs hsum)

lemma metaplecticCompletionEuler_inverse_differentiableOn {r : Eisenstein} (hr : r ≠ 0) :
    DifferentiableOn ℂ (fun s => (metaplecticCompletionEuler r s)⁻¹)
      {s : ℂ | (1/2:ℝ) < s.re} :=
  (metaplecticCompletionEuler_differentiableOn hr).inv
    (fun _ hs => metaplecticCompletionEuler_ne_zero hr hs)

end CubicFirstMoment

end

end OAI
