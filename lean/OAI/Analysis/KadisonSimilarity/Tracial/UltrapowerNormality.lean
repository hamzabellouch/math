import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerTraceBalls

namespace OAI

/-! The actual tracial ultrapower has closed bounded trace-vector balls,
hence its faithful GNS representation is a von Neumann algebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))
  (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hω in
theorem ultrapower_trace_balls_closed (C : ℝ) :
    IsClosed (gnsTracialVector (quotientTrace τ h1 ω htr) ''
      Metric.closedBall (0 : Ultrapower τ h1 ω htr) C) := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  apply IsSeqClosed.isClosed
  intro u ξ hu hlim
  choose X hX hXu using hu
  have hXC (n : ℕ) : ‖X n‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hX n
  have hC : 0 ≤ C := (norm_nonneg (X 0)).trans (hXC 0)
  have happrox (k : ℕ) : ∃ n, dist (u n) ξ ≤ (1 / 2 : ℝ) ^ k := by
    have hk : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds ξ hk)).exists
    exact ⟨n, hn.le⟩
  choose n hn using happrox
  have hrep (ε : ℝ) (hε : 0 < ε) :
      ∃ a : Ultrapower τ h1 ω htr, ‖a‖ ≤ C + ε ∧ V a = ξ := by
    choose x hx hxn using fun k =>
      HochschildCStarQuotient.norm_mk_lt (ideal τ h1 ω htr) (X (n k)) hε
    have hxC (k : ℕ) : ‖x k‖ ≤ C + ε := (hxn k).le.trans (add_le_add (hXC _) le_rfl)
    have htrace (k : ℕ) : V (q (x k)) = u (n k) := by
      change V (Ideal.Quotient.mk (ideal τ h1 ω htr) (x k)) = _
      rw [hx k]
      exact hXu _
    obtain ⟨y, hy, hlimit⟩ := exists_bounded_diagonal_trace_limit τ h1 ω htr hω x
      (C + ε) (by positivity) hxC ξ (fun k => by rw [htrace]; exact hn k)
    exact ⟨q y, (NonUnitalStarAlgHom.norm_apply_le q y).trans hy, hlimit⟩
  obtain ⟨a, _, ha⟩ := hrep 1 zero_lt_one
  refine ⟨a, ?_, ha⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hbeq⟩ := hrep ε hε
  have hab : a = b := gnsTracialVector_injective (quotientTrace τ h1 ω htr)
    (quotientTrace_faithful τ h1 ω htr) (ha.trans hbeq.symm)
  simpa only [hab] using hb

include hω in
theorem ultrapower_gns_normal_range :
    (quotientTrace τ h1 ω htr).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (quotientTrace τ h1 ω htr).gnsStarAlgHom).toStarSubalgebra :=
  (gnsTracialGeometry (quotientTrace τ h1 ω htr)
    (quotientTrace_tracial τ h1 ω htr)).normal_range_of_closed_trace_balls
      (ultrapower_trace_balls_closed τ h1 ω htr hω)

end KadisonSimilarity

end

end OAI
