import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedInjectionEquivFree
import OAI.Combinatorics.TriangleRemoval.Spectral.FallingFactorialNormalizedProduct

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma rootedTemplate_edges_card_le_sq {k : ℕ} (T : RootedTemplate k) :
    T.edges.card ≤ k^2 := by
  have hh : T.edges ⊆ completeGraph k := by
    intro e he
    exact mem_completeGraph.mpr (T.simple e he)
  exact (Finset.card_le_card hh).trans (by rw [card_completeGraph]; exact Nat.choose_le_pow k 2)

theorem rootedCount_initial_uniform_error (H : ℕ) {k n : ℕ} (hk : k ≤ H)
    (hn : H ≤ n) (hn2 : 2 ≤ n) (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    |rootedCount T ψ (completeGraph n) /
      rootedScaling T n (1-1/(n : ℝ))-1| ≤
      (2 : ℝ)^(H^2) * (2*(H : ℝ)^2)/(n : ℝ) := by
  have hr : T.roots.card ≤ k := by simpa using Finset.card_le_univ T.roots
  have hs : T.roots.card+(k-T.roots.card) = k := Nat.add_sub_of_le hr
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans
    (Nat.pow_le_pow_left hk 2)
  rw [rootedCount_completeGraph]
  unfold rootedScaling
  have hh := initialRootedScaling_error T.roots.card (k-T.roots.card) T.edges.card n
    (by rw [hs]; exact hk.trans hn) hn2
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  · rw [hs]
    have ha : (k-T.roots.card : ℕ) ≤ H := (Nat.sub_le _ _).trans hk
    have haR : ((k-T.roots.card : ℕ) : ℝ) ≤ H := by exact_mod_cast ha
    have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
    have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
    have hmul := mul_le_mul haR hkR (Nat.cast_nonneg k) (Nat.cast_nonneg H)
    nlinarith only [hmul,hbR]
  · positivity
  · positivity

end SharpTerminalLeave

end

end OAI
