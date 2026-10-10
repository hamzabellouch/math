import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerInteraction
import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

/-!
# Local Sobolev solutions in the Schrödinger interaction representation

The actual polynomial field satisfies the Banach-space Picard–Lindelöf
hypotheses. This establishes local existence without treating the nonlinear
Cauchy theory as an external assumption.
-/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- Local existence for the actual interaction equation in `H^k`. -/
theorem exists_sobolevInteractionSolution (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ → FourierL2, v 0 = f₀ ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t := by
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m (‖f₀‖ + 1) (by positivity)
  let T : ℝ := 1 / (A + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hnorm (f : FourierL2) (hf : f ∈ closedBall f₀ 1) : ‖f‖ ≤ ‖f₀‖ + 1 := by
    have hd : ‖f - f₀‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hf
    calc
      ‖f‖ = ‖(f - f₀) + f₀‖ := by congr 1; abel
      _ ≤ ‖f - f₀‖ + ‖f₀‖ := norm_add_le _ _
      _ ≤ ‖f₀‖ + 1 := by linarith
  let t₀ : Icc (-T) T := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (schrodingerInteractionField k hk m)
      t₀ f₀ 1 0 ⟨A, hA⟩ ⟨K, hK⟩ := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro f hf g hg
      rw [dist_eq_norm, dist_eq_norm]
      change ‖schrodingerInteractionField k hk m t f - schrodingerInteractionField k hk m t g‖ ≤
        K * ‖f - g‖
      exact hlip t f g (hnorm f hf) (hnorm g hg)
    · intro f hf
      exact ((continuous_schrodingerInteractionField k hk m).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht f hf
      exact hbound t f (hnorm f hf)
    · change A * max (T - 0) (0 - -T) ≤ (1 : ℝ) - 0
      simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
      dsimp [T]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < A + 1)).2
      linarith
  obtain ⟨v, hv₀, hv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨T, hT, v, hv₀, ?_⟩
  intro t ht
  exact (hv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end DefocusingNLS

end OAI
