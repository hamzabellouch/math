import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Vanishing exponential error for uniformly bounded word prefixes -/

noncomputable section
namespace PolycyclicRecognition

open Filter Module
open scoped Topology

/-- A constant coordinate radius can be written as an exponential envelope
whose normalized exponent tends to zero along the scale sequence. -/
theorem exists_vanishing_exponential_envelope
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (D : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, D ≤ Real.exp (scale n * ε n) := by
  let ε := fun n => Real.log (max D 1) / scale n
  have hm : 0 < max D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hs (n : ℕ) : 0 < scale n := lt_of_lt_of_le zero_lt_one (hscale1 n)
  refine ⟨ε, fun n => div_nonneg (Real.log_nonneg (le_max_right _ _)) (hs n).le,
    tendsto_const_nhds.div_atTop hscale, ?_⟩
  intro n
  have he : scale n * ε n = Real.log (max D 1) := by
    dsimp only [ε]
    field_simp [(hs n).ne']
  rw [he, Real.exp_log hm]
  exact le_max_left _ _

/-- Enlarging nonnegative word weights preserves the common prefix bound,
so all prefix coordinates satisfy the vanishing exponential error required
by neighboring-sheet affinity. The basis and weights may vary with scale. -/
theorem enlarged_prefix_vanishing_envelope
    {L J K : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : ℕ → Basis J ℝ L) (cost : ℕ → J → ℝ)
    (hcost : ∀ n j, 0 ≤ cost n j)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n)
    (vertex : ℕ → K → L) (D : ℝ)
    (hbound : ∀ n k,
      ‖(exponentialRescaleBasis (b n) (cost n) (scale n)).equivFun (vertex n k)‖ ≤ D)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n k,
        ‖(exponentialRescaleBasis (b n) (fun j => (1 + δ) * cost n j) (scale n)).equivFun
          (vertex n k)‖ ≤ Real.exp (scale n * ε n) := by
  obtain ⟨ε, hε0, hε, hD⟩ := exists_vanishing_exponential_envelope scale hscale hscale1 D
  refine ⟨ε, hε0, hε, ?_⟩
  intro n k
  have hb := norm_change_exponentialRescaleBasis_le (b n)
    (fun j => (1 + δ) * cost n j) (cost n) (by linarith [hscale1 n] : 0 ≤ scale n)
    (α := 0) (by intro j; nlinarith [mul_nonneg hδ (hcost n j)]) (vertex n k)
  simp only [mul_zero, Real.exp_zero, one_mul] at hb
  exact hb.trans ((hbound n k).trans (hD n))

end PolycyclicRecognition

end

end OAI
