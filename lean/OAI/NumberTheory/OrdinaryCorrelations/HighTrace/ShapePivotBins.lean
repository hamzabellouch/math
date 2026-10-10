import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BinWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PivotEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoreTupleBins

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.PivotSummation
open Finset Classical Filter
variable {h ℓ : ℕ} {w : ClosedLine h ℓ}

theorem shape_pivot_bins (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ Real.exp (B^r) < (p : ℝ)) →
      ∀ (n : ℕ) (Q : Fin n → Shape w), StrictMono (fun i => (Q i).topEdge) →
      ∀ (H : ℝ) (C : Fin n → ℝ), (∀ i, 0 < C i) →
      (∑ x : Fin n → ↥s,
        ∏ i, if H < C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then (x j : ℝ) else 1) ∧
          C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then (x j : ℝ) else 1) ≤ τ*H
          then (x i : ℝ)⁻¹ else 0) ≤ (((Real.log 4+1)*τ)/B^r)^n := by
  filter_upwards [core_tuple_bins r τ hr hτ] with B hB
  intro s hs n Q hQ H C hC
  let D : ∀ i : Fin n, (Fin i.val → ↥s) → ℝ := fun i pre =>
    C i * ∏ j : Fin i.val, if (Q i).topEdge ∈
      (Q ⟨j.val,lt_trans j.isLt i.isLt⟩).edges.val then (pre j : ℝ) else 1
  have hD : ∀ i pre, 0 < D i pre := by
    intro i pre
    apply mul_pos (hC i)
    apply prod_pos
    intro j hj
    split_ifs
    · exact_mod_cast (hs (pre j) (pre j).property).1.pos
    · exact zero_lt_one
  have he (x : Fin n → ↥s) (i : Fin n) :
      C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then (x j : ℝ) else 1) =
      (x i : ℝ)*D i (earlierTuple x i) := by
    rw [selected_prime_product Q hQ (fun j => (x j : ℝ)) i,
      earlier_product i]
    dsimp only [D,earlierTuple]
    ring
  simp_rw [he]
  exact hB s hs n H D hD

theorem chosen_pivot_bins (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ Real.exp (B^r) < (p : ℝ)) →
      ∀ {σ : Type*} (q : σ → Shape w) (core : σ → Prop)
        (H : ℝ) (C : Fin (pivotEdges q core).card → ℝ), (∀ i, 0 < C i) →
      (∑ x : Fin (pivotEdges q core).card → ↥s,
        ∏ i, if H < C i * ∏ j,
            (if (q (orderedPivot q core i)).topEdge ∈ (q (orderedPivot q core j)).edges.val
              then (x j : ℝ) else 1) ∧
          C i * ∏ j,
            (if (q (orderedPivot q core i)).topEdge ∈ (q (orderedPivot q core j)).edges.val
              then (x j : ℝ) else 1) ≤ τ*H
          then (x i : ℝ)⁻¹ else 0) ≤
        (((Real.log 4+1)*τ)/B^r)^(pivotEdges q core).card := by
  filter_upwards [shape_pivot_bins (w := w) r τ hr hτ] with B hB
  intro s hs σ q core H C hC
  exact hB s hs _ (fun i => q (orderedPivot q core i)) (orderedPivot_strictMono q core) H C hC

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
