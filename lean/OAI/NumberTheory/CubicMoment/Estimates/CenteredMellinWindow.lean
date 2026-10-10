import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductHeight

namespace OAI

/-! Transfer a centered polynomial bound through the actual finite
Mellin window and the original low-height weight. The complementary
Mellin tail is kept separate and is not bounded by this lemma. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def centeredMellinWindow (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (X S u : ℝ) : ℂ :=
  ∫ τ in Icc (-S) S, zeroLineMellinWeight W X τ*
    centeredProductPolynomial A B α β ℓ (u-τ)

theorem centeredMellinWindow_bound (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M) (S u : ℝ)
    (hb : ∀ τ ∈ Icc (-S) S, ‖centeredProductPolynomial A B α β ℓ (u-τ)‖ ≤ M) :
    ‖centeredMellinWindow A B α β ℓ W X S u‖ ≤ zeroLineMellinMass W*M := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hnorm : ‖centeredMellinWindow A B α β ℓ W X S u‖ ≤
      ∫ τ in Icc (-S) S, ‖zeroLineMellinWeight W X τ‖*M := by
    apply norm_integral_le_of_norm_le (hw.norm.mul_const M).restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb τ hτ) (_root_.norm_nonneg _)
  apply hnorm.trans
  rw [integral_mul_const]
  have hi : (∫ τ in Icc (-S) S, ‖zeroLineMellinWeight W X τ‖) ≤
      ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  rw [zeroLineMellinWeight_mass W hX] at hi
  exact mul_le_mul_of_nonneg_right hi hM

def centeredLowMellinWindow (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (X X₀ H T S : ℝ) : ℂ :=
  ∫ t : ℝ, lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
    centeredMellinWindow A B α β ℓ W X S t

theorem centeredLowMellinWindow_bound (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M) (X₀ H S : ℝ)
    (hb : ∀ t ∈ Icc (-(4/3)*T) ((4/3)*T), ∀ τ ∈ Icc (-S) S,
      ‖centeredProductPolynomial A B α β ℓ (t-τ)‖ ≤ M) :
    ‖centeredLowMellinWindow A B α β ℓ W X X₀ H T S‖ ≤
      (8/3)*Real.log 2*T*(zeroLineMellinMass W*M) := by
  have hm : 0 ≤ zeroLineMellinMass W := by
    rw [← zeroLineMellinWeight_mass W hX]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  have he : centeredLowMellinWindow A B α β ℓ W X X₀ H T S =
      ∫ t : ℝ, lowHeightWeight H T t*
        (Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
          centeredMellinWindow A B α β ℓ W X S t) := by
    unfold centeredLowMellinWindow
    congr 1
    funext t
    ring
  rw [he]
  apply lowHeightWeight_integral_bound H hT (mul_nonneg hm hM)
  intro t ht
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  exact centeredMellinWindow_bound A B α β ℓ W hW hpos hsm hX hM S t (hb t ht)

end CubicFirstMoment

end

end OAI
