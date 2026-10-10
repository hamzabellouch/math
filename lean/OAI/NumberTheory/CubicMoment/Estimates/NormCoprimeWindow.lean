import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeMellin
import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! Passing from a bounded range of Mellin shifts to the full coprime
Poisson integral, with the exact coarse envelope for its remaining shifts. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeMellinEnvelope (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) : ℝ :=
  ∑ s ∈ U.powerset, (H.card:ℝ)*
    ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2+
     (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)/2

lemma coprimeMellinEnvelope_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) :
    0 ≤ coprimeMellinEnvelope S H U v w := by
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num)

theorem normCoprimeRadialForm_window_bound (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (hx : ∀ h ∈ H, 1 ≤ x h) (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ B T : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hT : 0 < T) (k : ℕ)
    (hsmall : ∀ t, ‖t‖ ≤ T → coprimeMellinMass S H U v w y t ≤ B) :
    ‖normCoprimeRadialForm S H v w phase x y W ρ‖ ≤
      B*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖)+
      coprimeMellinEnvelope S H U v w/T^k*
        (∫ t : ℝ, ‖t‖^k*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) := by
  apply (normCoprimeRadialForm_norm_le_mass M hM S H U hS hU hSU v w phase hphase
    x y hx hy hlog W hW hW' hρ).trans
  exact integral_schwartz_window (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))
    (coprimeMellinMass_continuous S H U v w y)
    (coprimeMellinMass_nonneg S H U v w y) hB (coprimeMellinEnvelope_nonneg S H U v w)
    hT k (coprimeMellinMass_le_envelope S H U (fun a ha => (hS a ha).1) v w y) hsmall

end CubicFirstMoment

end

end OAI
