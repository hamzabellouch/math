import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GraphCoefficientStability

namespace OAI

/-! A uniform coefficient budget for the actual calibrated Hubbard graph.
The residual is measured against the analytic hopping target, while the
conclusion concerns the finite-spin variational bottom. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem calibrated_coefficient_uniform_error {a K gap τ ε g N U : ℝ}
    (hK : 0 ≤ K) (hKN : K ≤ N) (hg : 0 < g) (hgap : g ≤ gap) (hU : gap ≤ U)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hres : |a - τ * Real.sqrt (K * gap)| ≤ ε) :
    |a ^ 2 / gap - τ ^ 2 * K| ≤ ε * (2 * Real.sqrt (N * U) + ε) / g := by
  have hgapp : 0 < gap := hg.trans_le hgap
  have hε : 0 ≤ ε := (abs_nonneg _).trans hres
  have hN : 0 ≤ N := hK.trans hKN
  have hroot : Real.sqrt (K * gap) ≤ Real.sqrt (N * U) :=
    Real.sqrt_le_sqrt (mul_le_mul hKN hU hgapp.le hN)
  have htarget : τ * Real.sqrt (K * gap) ≤ Real.sqrt (N * U) :=
    (mul_le_mul_of_nonneg_right hτ1 (Real.sqrt_nonneg _)).trans (by simpa using hroot)
  have hnum : ε * (2 * τ * Real.sqrt (K * gap) + ε) ≤
      ε * (2 * Real.sqrt (N * U) + ε) := by
    apply mul_le_mul_of_nonneg_left _ hε
    linarith
  exact (calibrated_coefficient_error hK hgapp hτ hres).trans
    ((div_le_div_of_nonneg_right hnum hgapp.le).trans
      (div_le_div_of_nonneg_left (by positivity) hg hgap))

namespace HubbardGlobal
variable {Edge : Type*} [Fintype Edge]

theorem calibrated_graphSourceBottom_uniform_error
    (m : ℕ) (left right : Edge → Fin (m + 1))
    (t K gap : Edge → ℝ) {τ ε g N U : ℝ}
    (hK : ∀ e, 0 ≤ K e) (hKN : ∀ e, K e ≤ N)
    (hg : 0 < g) (hgap : ∀ e, g ≤ gap e) (hU : ∀ e, gap e ≤ U)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hres : ∀ e, |t e - τ * Real.sqrt (K e * gap e)| ≤ ε) :
    |graphSourceBottom m left right (fun e => t e ^ 2 / gap e) -
      graphSourceBottom m left right (fun e => τ ^ 2 * K e)| ≤
        4 * Fintype.card Edge * (ε * (2 * Real.sqrt (N * U) + ε) / g) := by
  apply (graphSourceBottom_stability m left right _ _).trans
  calc
    4 * ∑ e, |t e ^ 2 / gap e - τ ^ 2 * K e| ≤
        4 * ∑ _e : Edge, ε * (2 * Real.sqrt (N * U) + ε) / g := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun e _ => calibrated_coefficient_uniform_error
        (hK e) (hKN e) hg (hgap e) (hU e) hτ hτ1 (hres e))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
