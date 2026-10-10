import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeSW
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeVariation

namespace OAI

/-! The actual distinguished-coordinate prime sum follows from the
published prime input and the derived smooth detector variation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|)) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_interval_bound hEF ℓ hℓ hA hD
  obtain ⟨E,hE,hdet⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨2*C*(3+2*E),P₀,by positivity,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hsmooth,hnorm,hder⟩ := distinguishedRadialWeight_bounds W hW hM hV hE hw hz hWn hWd hdet
  obtain ⟨hdiff,hint,hvar⟩ := radial_mellin_interval_variation hsmooth hP0 (by norm_num)
    ha hab hb hM (by positivity) hnorm hder u
  have hU : 0 ≤ |u| := abs_nonneg u
  have hfac : 1 ≤ 2+2*E+|u| := by linarith
  have hfac' : 2+2*E+|u| ≤ (3+2*E)*(1+|u|) := by
    nlinarith [mul_nonneg (show 0 ≤ 2+2*E by positivity) hU]
  have hvar' : 2*M+(2-1)*((V+2*E*M)+M*|u|) ≤
      (3+2*E)*((M+V)*(1+|u|)) := by
    calc
      _ = (2+2*E+|u|)*M+V := by ring
      _ ≤ (2+2*E+|u|)*M+(2+2*E+|u|)*V :=
        add_le_add le_rfl (le_mul_of_one_le_left hV hfac)
      _ = (2+2*E+|u|)*(M+V) := by ring
      _ ≤ ((3+2*E)*(1+|u|))*(M+V) :=
        mul_le_mul_of_nonneg_right hfac' (add_nonneg hM hV)
      _ = _ := by ring
  calc
    _ ≤ (C*(2*P)/T^D)*(2*M+(2-1)*((V+2*E*M)+M*|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvar (by positivity))
    _ ≤ (C*(2*P)/T^D)*((3+2*E)*((M+V)*(1+|u|))) :=
      mul_le_mul_of_nonneg_left hvar' (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
