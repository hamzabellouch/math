import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactor

namespace OAI

/-! Above its deterministic spatial bound, the energy cap is inactive.
The resulting factor is exactly the hard spatial restriction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavityRestrictedFactor_eq_indicator {d k : ℕ} {X : Type*}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (Y : X → EuclideanSpace ℝ (Fin d)) (ε : X → Spin k) (x : X) :
    cavityRestrictedFactor K L C T B (Y x) (ε x) =
      {x | ‖Y x‖ ≤ B}.indicator (fun x => Real.exp (cavityLogFactor K L C (Y x) (ε x))) x := by
  have he : 1+‖Y x‖^2 ≤ 1+B^2 ↔ ‖Y x‖ ≤ B := by
    constructor
    · intro h
      exact (sq_le_sq₀ (norm_nonneg _) hB).mp (by linarith)
    · intro h
      have hs := (sq_le_sq₀ (norm_nonneg _) hB).mpr h
      linarith
  unfold cavityRestrictedFactor
  simp only [he]
  by_cases hx : ‖Y x‖ ≤ B
  · have hlog : cavityLogFactor K L C (Y x) (ε x) ≤ T :=
      (le_abs_self _).trans ((cavity_logFactor_growth K L C (Y x) (ε x)).trans
        ((mul_le_mul_of_nonneg_left (he.mpr hx) (cavityFactorSize_nonneg K L C)).trans hT))
    simp only [hx,ite_true,min_eq_left hlog]
    rw [Set.indicator_of_mem (show x ∈ {x | ‖Y x‖ ≤ B} from hx)]
  · simp only [hx,ite_false]
    rw [Set.indicator_of_notMem (show x ∉ {x | ‖Y x‖ ≤ B} from hx)]

end InvariantIsing

end

end OAI
