import OAI.Analysis.KadisonKastler.TraceVectorTransfer
import OAI.Analysis.KadisonKastler.RowPairing

namespace OAI

/-! # Weak operator convergence from tracial pairings -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B H J : Type*} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The norm-density property for arbitrary vector functionals. -/
def TracePairingApproximation (τ : FaithfulTracialState B)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ ξ η : H, ∀ ε : ℝ, 0 < ε → ∃ b : B, ∀ a : B,
    ‖inner ℂ ξ (ρ a η) - τ.toLinearMap (b * a)‖ ≤ ε * ‖a‖

theorem TracePairingApproximation.vector
    {τ : FaithfulTracialState B} {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (h : TracePairingApproximation τ ρ) : TraceVectorApproximation τ ρ :=
  fun z => h z z

/-- On a bounded set, convergence of all trace pairings implies weak
operator convergence in any representation with the density property. -/
theorem TracePairingApproximation.weakOperatorConverges
    {τ : FaithfulTracialState B} {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (h : TracePairingApproximation τ ρ)
    (l : Filter J) (x : J → B) (a : B) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ j, ‖x j‖ ≤ C)
    (htrace : ∀ b : B, Tendsto (fun j => τ.toLinearMap (b * x j)) l
      (𝓝 (τ.toLinearMap (b * a)))) :
    WeakOperatorConverges l (fun j => ρ (x j)) (ρ a) := by
  intro ξ η
  have hlin : Tendsto (fun j => inner ℂ η (ρ (x j) ξ)) l
      (𝓝 (inner ℂ η (ρ a ξ))) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let α := ε / (3 * (C + ‖a‖ + 1))
    have hα : 0 < α := by dsimp [α]; positivity
    obtain ⟨b, hb⟩ := h η ξ α hα
    have heq : α * (3 * (C + ‖a‖ + 1)) = ε := by
      dsimp [α]
      exact div_mul_cancel₀ _ (by positivity)
    have ht := (Metric.tendsto_nhds.mp (htrace b)) (ε / 3) (by positivity)
    filter_upwards [ht] with j hj
    rw [dist_eq_norm] at hj ⊢
    have h1 := (hb (x j)).trans (mul_le_mul_of_nonneg_left (hx j) hα.le)
    have h3 : ‖τ.toLinearMap (b * a) - inner ℂ η (ρ a ξ)‖ ≤ α * ‖a‖ := by
      rw [norm_sub_rev]
      exact hb a
    have hsplit : inner ℂ η (ρ (x j) ξ) - inner ℂ η (ρ a ξ) =
        (inner ℂ η (ρ (x j) ξ) - τ.toLinearMap (b * x j)) +
        (τ.toLinearMap (b * x j) - τ.toLinearMap (b * a)) +
        (τ.toLinearMap (b * a) - inner ℂ η (ρ a ξ)) := by ring
    rw [hsplit]
    have hbound := (norm_add_le
      ((inner ℂ η (ρ (x j) ξ) - τ.toLinearMap (b * x j)) +
      (τ.toLinearMap (b * x j) - τ.toLinearMap (b * a)))
      (τ.toLinearMap (b * a) - inner ℂ η (ρ a ξ))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    nlinarith
  have hc := hlin.star
  simpa only [← starRingEnd_apply, inner_conj_symm] using hc

end

end KadisonKastler

end OAI
