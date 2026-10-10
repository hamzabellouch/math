import OAI.Analysis.KadisonKastler.ConcreteTraceComplete
import OAI.Analysis.KadisonKastler.TraceLimits

namespace OAI

/-! # Projections obtained as bounded tracial limits -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Selfadjoint contractive two-Cauchy sequences with vanishing
idempotency defect converge to a projection in the original algebra. -/
theorem FiniteVectorTrace.projection_limit
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (x : ℕ → Algebra M) (hx : ∀ j, ‖x j‖ ≤ 1)
    (hsa : ∀ j, IsSelfAdjoint (x j))
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε)
    (hdefect : Tendsto (fun j => traceTwoNorm τ (x j * x j - x j)) atTop (𝓝 0)) :
    ∃ e : Algebra M, IsStarProjection e ∧ ‖e‖ ≤ 1 ∧
      (∀ ξ, Tendsto (fun j => (x j : H →L[ℂ] H) ξ) atTop
        (𝓝 ((e : H →L[ℂ] H) ξ))) ∧
      Tendsto (fun j => traceTwoNorm τ (x j - e)) atTop (𝓝 0) := by
  obtain ⟨e, he, hs, h2⟩ := hτ.bounded_complete x (by norm_num) hx hCauchy
  have hstar : Tendsto (fun j => traceTwoNorm τ (x j - star e)) atTop (𝓝 0) := by
    have heq (j : ℕ) : traceTwoNorm τ (x j - star e) = traceTwoNorm τ (x j - e) := by
      calc
        _ = traceTwoNorm τ (star (x j - e)) := by rw [star_sub, (hsa j).star_eq]
        _ = _ := traceTwoNorm_star τ _
    simpa only [heq] using h2
  have heStar : star e = e := traceTwoNorm_limit_unique τ x hstar h2
  have hmul := traceTwoNorm_tendsto_mul τ x x e e hx h2 h2
  have hb (j : ℕ) : traceTwoNorm τ (e * e - e) ≤
      traceTwoNorm τ (x j * x j - e * e) +
      traceTwoNorm τ (x j * x j - x j) + traceTwoNorm τ (x j - e) := by
    have heq : e * e - e =
        -(x j * x j - e * e) + (x j * x j - x j) + (x j - e) := by noncomm_ring
    rw [heq]
    exact (traceTwoNorm_add_le τ _ _).trans (add_le_add
      (by simpa only [traceTwoNorm_neg] using
        traceTwoNorm_add_le τ (-(x j * x j - e * e)) (x j * x j - x j)) le_rfl)
  have hz : traceTwoNorm τ (e * e - e) ≤ 0 :=
    ge_of_tendsto (by simpa only [zero_add] using (hmul.add hdefect).add h2)
      (Eventually.of_forall hb)
  have heMul : e * e = e := sub_eq_zero.mp ((traceTwoNorm_eq_zero_iff τ _).mp
    (le_antisymm hz (traceTwoNorm_nonneg τ _)))
  exact ⟨e, ⟨heMul, heStar⟩, he, hs, h2⟩

end

end KadisonKastler

end OAI
