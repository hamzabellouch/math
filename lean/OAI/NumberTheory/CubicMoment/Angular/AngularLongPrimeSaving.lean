import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeMoebius
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeMoebius
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimePowers

namespace OAI

/-! Every fixed power saving for the literal free prime, with the
polynomial norm-twist and excluded-prime costs already absorbed. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_moebius_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_moebius_bound hEF ℓ hℓ hA (add_pos_of_pos_of_nonneg hD hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := E)
      (inv_nonneg.mpr hlog2.le) hD.le hE)
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e hc hs hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hTH : 1 ≤ T^H := Real.one_le_rpow hT hH
  have hheight : 1+|u| ≤ 2*T^H := by linarith
  have hmain : K*P/T^(D+H)*(1+|u|) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+H)*(2*T^H) :=
        mul_le_mul_of_nonneg_left hheight (by positivity)
      _ = 2*K*P/T^D := by
        rw [Real.rpow_add hT0]
        field_simp
  have herror : Real.log (norm (c*e))/Real.log 2 ≤ P/T^D := by
    calc
      _ ≤ T^E/Real.log 2 := (div_le_div_iff_of_pos_right hlog2).mpr hNe
      _ = (Real.log 2)⁻¹*T^E := by ring
      _ ≤ P/T^D := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w u hT ((le_max_left _ _).trans hP) hTP ha hab hb hw
    c v e hc hs hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
