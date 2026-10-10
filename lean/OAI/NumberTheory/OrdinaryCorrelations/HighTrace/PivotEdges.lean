import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Nonempty

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ} {w : ClosedLine h ℓ} {σ : Type*}

def pivotEdges (q : σ → Shape w) (core : σ → Prop) : Finset (Fin ℓ) :=
  (goodEdges w).filter (fun e => ∃ s, core s ∧ (q s).top.val=w.offset e.castSucc)

lemma pivot_exists (q : σ → Shape w) (core : σ → Prop) (e : ↥(pivotEdges q core)) :
    ∃ s, core s ∧ (q s).top.val=w.offset e.val.castSucc := (mem_filter.mp e.property).2

def choosePivot (q : σ → Shape w) (core : σ → Prop) (e : ↥(pivotEdges q core)) : σ :=
  Classical.choose (pivot_exists q core e)

lemma choosePivot_spec (q : σ → Shape w) (core : σ → Prop) (e : ↥(pivotEdges q core)) :
    core (choosePivot q core e) ∧
      (q (choosePivot q core e)).top.val=w.offset e.val.castSucc :=
  Classical.choose_spec (pivot_exists q core e)

lemma choosePivot_topEdge (q : σ → Shape w) (core : σ → Prop) (e : ↥(pivotEdges q core)) :
    (q (choosePivot q core e)).topEdge=e.val := by
  have hg : w.Good e.val := (mem_filter.mp (mem_filter.mp e.property).1).2
  have ht := (choosePivot_spec q core e).2
  symm
  apply Shape.unary_edge_eq_topEdge (q (choosePivot q core e))
  · rw [ht]
    exact hg.2.1
  · exact hg.1
  · exact ht.symm

def pivotOrder (q : σ → Shape w) (core : σ → Prop) :
    Fin (pivotEdges q core).card ≃o ↥(pivotEdges q core) := (pivotEdges q core).orderIsoOfFin rfl

def orderedPivot (q : σ → Shape w) (core : σ → Prop)
    (i : Fin (pivotEdges q core).card) : σ := choosePivot q core (pivotOrder q core i)

lemma orderedPivot_core (q : σ → Shape w) (core : σ → Prop)
    (i : Fin (pivotEdges q core).card) : core (orderedPivot q core i) :=
  (choosePivot_spec q core _).1

lemma orderedPivot_strictMono (q : σ → Shape w) (core : σ → Prop) :
    StrictMono (fun i => (q (orderedPivot q core i)).topEdge) := by
  intro i j hij
  simp only [orderedPivot,choosePivot_topEdge]
  exact (pivotOrder q core).strictMono hij

lemma orderedPivot_injective (q : σ → Shape w) (core : σ → Prop) :
    Function.Injective (orderedPivot q core) := by
  intro i j hij
  apply (orderedPivot_strictMono q core).injective
  exact congrArg (fun s => (q s).topEdge) hij

theorem chosen_prime_product (q : σ → Shape w) (core : σ → Prop)
    (x : Fin (pivotEdges q core).card → ℝ) (i : Fin (pivotEdges q core).card) :
    (∏ j, if (q (orderedPivot q core i)).topEdge ∈ (q (orderedPivot q core j)).edges.val
      then x j else 1) = x i *
        ∏ j ∈ univ.filter (fun j => j < i),
          if (q (orderedPivot q core i)).topEdge ∈ (q (orderedPivot q core j)).edges.val
          then x j else 1 :=
  selected_prime_product (fun j => q (orderedPivot q core j)) (orderedPivot_strictMono q core) x i

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
