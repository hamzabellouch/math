import OAI.Probability.BenjaminiSchramm.LayerMaximumDecomposition
import OAI.Probability.BenjaminiSchramm.BoundedLayerShift

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem supAdjustedFullLayerMoment_le_row_bound
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C) (i : ℤ) :
    G.supAdjustedFullLayerMoment a R p i ≤ C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact restrictedLayerCount_expectation_le_row_bound G.ends p C hrow _ _ x

theorem adjustedFullLayerMoment_up_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p (n : ℤ) x u ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  by_cases hn : n=0
  · subst n
    have hz : (1 : ℝ≥0∞) ≤ G.supAdjustedUpLayerMoment a R p 0 :=
      (G.adjustedUpLayerMoment_zero_ge_one a R p x u).trans (G.adjustedUpLayerMoment_le_sup a R p 0 x u)
    exact ((G.adjustedFullLayerMoment_le_sup a R p 0 x u).trans
      (G.supAdjustedFullLayerMoment_le_row_bound a R p C hrow 0)).trans
        ((one_mul C).symm.le.trans (mul_le_mul' hz le_rfl))
  let f := G.adjustedLayerIndex a R u x
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by
    simp only [f,G.adjustedLayerIndex_self]
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hA : ∀ y ∈ {v | f v=(n : ℤ)}, (n : ℤ) ≤ f y := fun _ h => h.ge
  exact (first_layer_moment_bound_with_row G.ends p C hrow f hj Set.univ _ x n hx hA).trans
    (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p n x u) le_rfl)

theorem supAdjustedFullLayerMoment_up_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C) (n : ℕ) :
    G.supAdjustedFullLayerMoment a R p (n : ℤ) ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact G.adjustedFullLayerMoment_up_bound hc hl a R hR hjump p C hrow n x u

end CriticalPercolation.BondGraph

end

end OAI
