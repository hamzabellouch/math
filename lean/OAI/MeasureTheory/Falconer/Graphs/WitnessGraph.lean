import OAI.MeasureTheory.Falconer.Graphs.DyadicGraph
import OAI.MeasureTheory.Falconer.Estimates.DyadicAncestors

namespace OAI

/-!
# Schur bound from the original parallel-test witnesses

For each endpoint, all retained cells in an ancestor group are charged
to one actual eligible witness. Combining both candidate bounds with the
center tests gives the smaller of the two profile counts.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def DyadicParallelTest {d : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (g : ℕ) (a : List (Fin d → Bool))
    (w : Space d) (W : ℝ) (C : ℕ) : Prop :=
  (A.filter (fun z => z.take g = a.take g ∧
    ‖(Q.descendant z).center - (Q.descendant a).center‖ ≤
      Real.sqrt d * (Q.side/(2 : ℝ)^g) ∧
    ‖perpendicularPart w ((Q.descendant z).center - (Q.descendant a).center)‖ ≤ W)).card ≤ C

def DyadicCapWitnesses {d : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (g : ℕ)
    (w₀ : Space d) (δ W : ℝ) (C : ℕ) : Prop :=
  ∀ a ∈ A, ∃ w : Space d, ‖w‖ = 1 ∧ ‖w-w₀‖ ≤ δ ∧ DyadicParallelTest Q A g a w W C

theorem retainedDyadic_witness_schur {d n g₁ g₂ L C₁ C₂ : ℕ}
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
    (F : List (Fin d → Bool) × List (Fin d → Bool) → ℂ) :
    (∑ row ∈ A ×ˢ B, ∑ col ∈ A ×ˢ B,
      if retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col then ‖F row * star (F col)‖ else 0) ≤
      ((2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) : ℕ) *
        ∑ row ∈ A ×ˢ B, ‖F row‖^2 := by
  apply retainedDyadic_schur Q₁ Q₂ hQ hside A B hA hB w₁ w₂ hw₁ hw₂ τ hL
  · intro a _
    exact Q₁.parallel_count hQ A hA hg₁ w₁ (Q₁.descendant a).center hw₁ hδ hwidth₁ htest₁
  · intro a _
    have hQ₂ : 0 < Q₂.side := hside.symm ▸ hQ
    exact Q₂.parallel_count hQ₂ B hB hg₂ w₂ (Q₂.descendant a).center hw₂ hδ hwidth₂ htest₂

end Falconer

end OAI
