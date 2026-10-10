import Mathlib
import OAI.Probability.Ballisticity.Estimates.SingleThreat

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem fresh_budget_threat_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam C D : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧ 0 < D ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i f.1 - x j f.1|) →
        ∀ (H : ℕ) (z s : ℝ), 0 < z → Real.exp (-Bstar) ≤ s →
        (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
          Real.exp (C*k)*s^lam + D*k*H /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) z / s := by
  obtain ⟨lam,C,hlam,hlam1,hC,hinv⟩ :=
    separated_initial_inverse_moment ν hue (realPosition (step e)) (signed_direction_unit e) htrans f.1
  let p := (annealedLaw ν).real (NoDrop (realPosition (step e)) 0)
  have hp : 0 < p := ENNReal.toReal_pos
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)) (measure_ne_top _ _)
  refine ⟨lam,C,10/p^2,hlam,hlam1,hC,by positivity,?_⟩
  intro Bstar hB k hk
  obtain ⟨G,hG⟩ := hinv Bstar hB k hk
  refine ⟨G,?_⟩
  intro π hπ hsep H z s hz hs
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  let hp' := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
  let b := fun j => (recordMedian ν (realPosition (step e)) hp' f j:ℝ)
  have hq : (environmentLaw ν).real
      {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} ≤ Real.exp (C*k)*s^lam := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hG π hsep s hs)
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _))] at h
    exact h
  have hf := annealed_median_failure_bound ν e f htrans H hz
  dsimp only at hf
  have hb := single_budget_threat_bound ν e f htrans H b z hs0 π
  apply hb.trans (add_le_add hq ?_)
  apply (div_le_div_iff_of_pos_right hs0).mpr
  calc
    _ ≤ (k:ℝ)*((10/p^2)*(H:ℝ)/fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) z) :=
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg k)
    _ = _ := by ring

end DirectionalTransience

end

end OAI
