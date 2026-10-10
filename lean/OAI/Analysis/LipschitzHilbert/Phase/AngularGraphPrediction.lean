import OAI.Analysis.LipschitzHilbert.Phase.AngularCountBridge
import OAI.Analysis.LipschitzHilbert.Phase.GraphPhaseAverage

namespace OAI

/-! Geometric angular graphs meet the hypotheses of the Fourier prediction. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem subtype_independent_card_le (g : AngularGrid) (level : ℕ) (gap : ℝ)
    (cells : Finset ℤ) (D : ℝ)
    (hcard : ∀ S : Finset ℤ, S ⊆ cells →
      (S : Set ℤ).Pairwise (fun c e => ¬g.neighbors level gap c e) → (S.card : ℝ) ≤ D)
    (S : Finset cells)
    (hS : (S : Set cells).Pairwise (fun c e => ¬g.neighbors level gap c.val e.val)) :
    (S.card : ℝ) ≤ D := by
  classical
  have hsub : S.image Subtype.val ⊆ cells := by
    intro c hc
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hc
    exact e.property
  have hpair : ((S.image Subtype.val : Finset ℤ) : Set ℤ).Pairwise
      (fun c e => ¬g.neighbors level gap c e) := by
    intro c hc e he hce
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact hS hc' he' (fun h => hce (congrArg Subtype.val h))
  have h := hcard (S.image Subtype.val) hsub hpair
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h

/-- The actual carrier frequencies inherit their gap from angular
nonneighbors; the graph cardinality comes from the common spatial
count, applied to finite subcollections of these cells. -/
theorem angular_graph_prediction_average {κ : Type*} [Fintype κ]
    (g : AngularGrid) (level : ℕ) (cells : Finset ℤ)
    {gap etaMin D p : ℝ}
    (w m : cells → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood
      (fun i j : cells => g.neighbors level gap i.val j.val) i) ≤ m i)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : ℝ) (eta : κ → ℝ) (l : cells → ℝ)
    (X : cells → EuclideanSpace ℂ κ) (lambda : cells → ℂ)
    (hgap : 0 < gap) (hetaMin : 0 < etaMin)
    (heta : ∀ k, etaMin ≤ |eta k|)
    (hν : PhaseCombinatorics.FourierGap ν (gap * etaMin)) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hcard : ∀ S : Finset ℤ, S ⊆ cells →
      (S : Set ℤ).Pairwise (fun c e => ¬g.neighbors level gap c e) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ PhaseCombinatorics.phaseMu D p) :
    (∫ t, (1 + ‖PhaseCombinatorics.diagonalFourierSum
      (fun i k => (s - g.center level i.val) * eta k)
      (fun i => (((l i ^ (1 - PhaseCombinatorics.phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  apply graph_weighted_diagonal_prediction_average
    (fun i j : cells => g.neighbors level gap i.val j.val)
    (fun {_ _} h => g.neighbors_symmetric level gap h) w m hw
    (fun i => by
      convert hm i using 1
      congr 1
      ext j
      simp only [mem_closedNeighborhood]) ν
    (fun i k => (s - g.center level i.val) * eta k) l X lambda
    (mul_pos hgap hetaMin) hν hD hp
  · intro i j _ hfar k
    exact g.carrier_frequency_separated level hetaMin.le (heta k) hfar
  · exact g.subtype_independent_card_le level gap cells D hcard
  · exact hl
  · exact htotal
  · exact hlambda

end LipschitzHilbert.AngularGrid

end

end OAI
