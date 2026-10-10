import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductGaussTail
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductModelTail

namespace OAI

/-! Exact phases in the product Mellin integral. The scale oscillation is
kept outside the fixed Schwartz profile, so its derivative cost is uniform. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def reflectedZeroMellinProfile (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) : SchwartzMap ℝ ℂ :=
  (1/(2*Real.pi):ℝ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv)
      (mellinVerticalSchwartz V hV hpos hsm 0)

lemma reflectedZeroMellinProfile_apply (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) (t : ℝ) :
    reflectedZeroMellinProfile V hV hpos hsm t = zeroLineMellinWeight V 1 (-t) := by
  simp only [reflectedZeroMellinProfile,smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.coe_neg,
    mellinVerticalSchwartz_apply,Complex.ofReal_zero,zero_add,
    zeroLineMellinWeight,Complex.ofReal_one,Complex.one_cpow,mul_one,Complex.real_smul]

lemma zeroLineMellinWeight_reflected_phase (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    zeroLineMellinWeight V X (-t) = reflectedZeroMellinProfile V hV hpos hsm t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I) := by
  rw [reflectedZeroMellinProfile_apply]
  simp only [zeroLineMellinWeight,Complex.ofReal_one,Complex.one_cpow,mul_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    ←Complex.ofReal_log hX.le]
  congr 1
  push_cast
  ring

lemma gaussProduct_shift (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b) (u t : ℝ) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) =
    ∑ a ∈ P, ∑ b ∈ B, (α a*normTwist u a)*(β b*normTwist u b)*
      gauss (a*b)*normTwist t (a*b) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hsum : normTwist (u+t) (a*b) = normTwist u (a*b)*normTwist t (a*b) := by
    simpa only [normTwist_eq_mellinPhase] using mellinPhase_add_height u t (norm (a*b))
  rw [hsum,normTwist_mul u (primary_ne_zero (hP a ha)) (primary_ne_zero (hB b hb))]
  ring

lemma norm_twisted_coefficient (α : Eisenstein → ℂ) (u : ℝ) (a : Eisenstein) :
    ‖α a*normTwist u a‖ = ‖α a‖ := by
  rw [norm_mul,norm_normTwist,mul_one]

end CubicFirstMoment

end

end OAI
