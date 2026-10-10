import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundary
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem exists_ineligible (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) :
    ∃ n : ℕ, ¬g.eligible cutoff precision n := by
  have hG : (1 : ℝ) < g.branching := by
    exact_mod_cast (show 1 < g.branching by have := g.branching_ge_two; omega)
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near
    (le_max_left 1 (cutoff / precision)) hG
  refine ⟨n + 1, ?_⟩
  unfold eligible
  have h := (div_lt_iff₀ hp).mp ((le_max_right 1 (cutoff / precision)).trans_lt hn)
  nlinarith

def lastEligible (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) : ℕ :=
  Nat.find (g.exists_ineligible cutoff precision hp) - 1

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

theorem eligible_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) :
    g.eligible cutoff precision (g.lastEligible cutoff precision hp) :=
  (g.eligible_iff_le_lastEligible cutoff precision hp hstart _).mpr le_rfl

theorem lastEligible_antitone_precision (g : AngularGrid) (cutoff p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hstartp : g.eligible cutoff p 0) (hstartq : g.eligible cutoff q 0) :
    g.lastEligible cutoff q hq ≤ g.lastEligible cutoff p hp := by
  apply (g.eligible_iff_le_lastEligible cutoff p hp hstartp _).mp
  have hqelig := g.eligible_lastEligible cutoff q hq hstartq
  exact (mul_le_mul_of_nonneg_right hpq (by positivity)).trans hqelig

end LipschitzHilbert.AngularGrid

end

end OAI
