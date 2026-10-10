import OAI.MeasureTheory.Falconer.Estimates.Eligibility
import OAI.MeasureTheory.Falconer.Graphs.WitnessGraph

namespace OAI

/-!
# The graph of eligible original cell--cap incidences

Support of an endpoint symbol in a literal parallel test supplies the
witnesses used by the degree estimate. Eligibility only filters the finite
cell list; no angular support is cut by a pointwise edge decision.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def DyadicCube.eligiblePaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) : Finset (List (Fin d → Bool)) :=
  (Q.occupiedPaths μ n).filter fun p =>
    0 < capIncidence (μ.restrict (Q.descendant p).carrier) η b

theorem DyadicCube.eligiblePaths_subset {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) :
    Q.eligiblePaths μ n η b ⊆ Q.occupiedPaths μ n := Finset.filter_subset _ _

theorem DyadicParallelTest.mono {d g C : ℕ} (Q : DyadicCube d)
    {A B : Finset (List (Fin d → Bool))} (hAB : A ⊆ B)
    (p : List (Fin d → Bool)) (w : Space d) (W : ℝ)
    (h : DyadicParallelTest Q B g p w W C) : DyadicParallelTest Q A g p w W C :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hAB)).trans h

theorem DyadicCube.eligiblePaths_witnesses {d n g C : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) (w₀ : Space d) (δ W : ℝ)
    (hη : ∀ w, 0 ≤ η w)
    (hcap : ∀ w, 0 < η w → ‖(w : Space d)-w₀‖ ≤ δ)
    (hsupport : ∀ p ∈ Q.occupiedPaths μ n,
      ∀ᵐ x ∂μ.restrict (Q.descendant p).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q (Q.occupiedPaths μ n) g p (w : Space d) W C) :
    DyadicCapWitnesses Q (Q.eligiblePaths μ n η b) g w₀ δ W C := by
  intro p hp
  obtain ⟨hpocc,hpinc⟩ := Finset.mem_filter.mp hp
  obtain ⟨x,w,hx,hw,hbw⟩ := capIncidence_witness
    (μ.restrict (Q.descendant p).carrier) η b hη _ (hsupport p hpocc) hpinc
  exact ⟨w, sphere_norm w, hcap w hw,
    DyadicParallelTest.mono Q (Q.eligiblePaths_subset μ n η b) p w W (hx w hbw)⟩

def eligibleDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (A B : Finset (List (Fin d → Bool))) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  row ∈ A ×ˢ B ∧ col ∈ A ×ˢ B ∧ retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col

theorem eligibleDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (A B : Finset (List (Fin d → Bool))) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row col ↔
      eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ col row := by
  simp only [eligibleDyadicEdge, retainedDyadicEdge_symm Q₁ Q₂ w₁ w₂ τ row col]
  tauto

/-- The degree bound holds inside any larger row list. Ineligible rows
have degree zero; eligible rows are bounded using their original witnesses. -/
theorem eligibleDyadic_degree {d n g₁ g₂ L C₁ C₂ : ℕ}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    (hg₁ : g₁ ≤ n) (hg₂ : g₂ ≤ n)
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    {τ δ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (htest₁ : DyadicCapWitnesses Q₁ A g₁ w₁ δ W₁ C₁)
    (htest₂ : DyadicCapWitnesses Q₂ B g₂ w₂ δ W₂ C₂)
    (S : Finset (List (Fin d → Bool) × List (Fin d → Bool)))
    (row : List (Fin d → Bool) × List (Fin d → Bool)) :
    (S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row)).card ≤
      (2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) := by
  by_cases hr : row ∈ A ×ˢ B
  · have hsub : S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row) ⊆
        (A ×ˢ B).filter (retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row) := by
      intro col hcol
      obtain ⟨_,hcol,hedge⟩ := (Finset.mem_filter.mp hcol).2
      exact Finset.mem_filter.mpr ⟨hcol,hedge⟩
    apply (Finset.card_le_card hsub).trans
    apply retainedDyadic_degree Q₁ Q₂ hQ hside A B hA hB w₁ w₂ hw₁ hw₂ τ hL row hr
    · exact Q₁.parallel_count hQ A hA hg₁ w₁ (Q₁.descendant row.1).center
        hw₁ hδ hwidth₁ htest₁
    · exact Q₂.parallel_count (hside.symm ▸ hQ) B hB hg₂ w₂ (Q₂.descendant row.2).center
        hw₂ hδ hwidth₂ htest₂
  · have hz : S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro col _ h
      exact hr h.1
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
