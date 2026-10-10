import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PivotEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Unselected
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SlotWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.PivotSummation
open OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
variable {h ℓ : ℕ} {w : ClosedLine h ℓ} {σ : Type*} [Fintype σ]

def slotEdgeProduct (q : σ → Shape w) (S : PrimeSystem) (x : σ → S.Index) (e : Fin ℓ) : ℝ :=
  ∏ s, if e ∈ (q s).edges.val then ((x s).val : ℝ) else 1

def pivotBinIndicator (q : σ → Shape w) (core : σ → Prop)
    (S : PrimeSystem) (C : Fin ℓ → ℝ) (H τ : ℝ) (x : σ → S.Index) : ℝ :=
  ∏ i : Fin (pivotEdges q core).card,
    if H < C (q (orderedPivot q core i)).topEdge *
        slotEdgeProduct q S x (q (orderedPivot q core i)).topEdge ∧
      C (q (orderedPivot q core i)).topEdge *
        slotEdgeProduct q S x (q (orderedPivot q core i)).topEdge ≤ τ*H then 1 else 0

theorem named_prime_sum (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (S : PrimeSystem),
      (∀ p ∈ S.core, Real.exp (B^r) < (p : ℝ)) →
      ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ) (σ : Type) [Fintype σ],
      ∀ (q : σ → Shape w) (core : σ → Prop) (C : Fin ℓ → ℝ),
      (∀ e, 0 < C e) → ∀ H : ℝ,
      (∑ x : σ → S.Index, pivotBinIndicator q core S C H τ x *
        ∏ s, slotWeight S (core s) (x s)) ≤
      (((Real.log 4+1)*τ)/B^r)^(pivotEdges q core).card *
        ∏ s : Unselected (orderedPivot q core),
          if core s.val then S.harmonicCore else S.harmonicCenter := by
  filter_upwards [shape_system_bins r τ hr hτ] with B hB
  intro S hS h ℓ w σ _ q core C hC H
  let sel := orderedPivot q core
  have hs : Function.Injective sel := orderedPivot_injective q core
  rw [show (∏ s : Unselected sel, if core s.val then S.harmonicCore else S.harmonicCenter) =
      ∏ s : Unselected sel, ∑ p : S.Index, slotWeight S (core s.val) p by
        simp_rw [slotWeight_sum]]
  apply slots_weighted_bound sel hs (fun s p => slotWeight S (core s) p)
    (fun s p => slotWeight_nonneg S _ p)
  intro z
  let Q : Fin (pivotEdges q core).card → Shape w := fun i => q (sel i)
  let D : Fin (pivotEdges q core).card → ℝ := fun i =>
    C (Q i).topEdge * ∏ s : Unselected sel,
      if (Q i).topEdge ∈ (q s.val).edges.val then ((z s).val : ℝ) else 1
  have hD : ∀ i, 0 < D i := by
    intro i
    apply mul_pos (hC _)
    apply prod_pos
    intro s hs
    split_ifs
    · exact_mod_cast (S.prime_mem (z s).val (z s).property).pos
    · exact zero_lt_one
  have he (y : Fin (pivotEdges q core).card → S.Index) (i : Fin (pivotEdges q core).card) :
      C (Q i).topEdge * slotEdgeProduct q S (mergeSlots sel hs y z) (Q i).topEdge =
      D i * ∏ j, if (Q i).topEdge ∈ (Q j).edges.val then ((y j).val : ℝ) else 1 := by
    unfold slotEdgeProduct
    rw [prod_slots sel hs]
    simp only [mergeSlots_selected,mergeSlots_unselected]
    dsimp only [D,Q]
    ring
  have heq : (∑ y : Fin (pivotEdges q core).card → S.Index,
      pivotBinIndicator q core S C H τ (mergeSlots sel hs y z) *
        ∏ i, slotWeight S (core (sel i)) (y i)) =
      ∑ y : Fin (pivotEdges q core).card → S.Index,
        ∏ i, if S.IsCore (y i) ∧
          H < D i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then ((y j).val : ℝ) else 1) ∧
          D i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then ((y j).val : ℝ) else 1) ≤ τ*H
          then ((y i).val : ℝ)⁻¹ else 0 := by
    apply sum_congr rfl
    intro y hy
    unfold pivotBinIndicator
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hc := orderedPivot_core q core i
    change core (sel i) at hc
    change ((if H < C (Q i).topEdge * slotEdgeProduct q S _ (Q i).topEdge ∧
      C (Q i).topEdge * slotEdgeProduct q S _ (Q i).topEdge ≤ τ*H then (1 : ℝ) else 0) *
      slotWeight S (core (sel i)) (y i)) = _
    rw [he y i]
    simp only [slotWeight,hc,true_iff]
    split_ifs <;> simp_all
  rw [heq]
  exact hB S hS h ℓ w _ Q (orderedPivot_strictMono q core) H D hD

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
