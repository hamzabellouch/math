import OAI.Combinatorics.Ryser.LineCover.CleanCover
import OAI.Combinatorics.Ryser.LineCover.TupleConcentration

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodTuples (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) : Prop :=
  ∀ a : LineTuple F t, AdmissibleTuple process.shapes D h a →
    δ * (t : ℝ) ^ 2 / 2 ≤ retainedCount (tupleShapes a) (crossPoints a) ω

theorem not_goodTuples_iff (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) :
    ¬ GoodTuples process h t ω ↔
      ∃ a : LineTuple F t, AdmissibleTuple process.shapes D h a ∧
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  simp only [GoodTuples, not_forall, not_le, exists_prop]

theorem prob_not_goodTuples_le_tuple_card (process : DeletionProcess F D δ)
    (h t : ℕ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) :
    process.law.prob (fun ω => ¬ GoodTuples process h t ω) ≤
      2 * (Fintype.card (LineTuple F t) : ℝ) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  calc
    _ ≤ process.law.prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple process.shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) := by
      apply process.law.prob_mono
      intro ω hω
      exact (not_goodTuples_iff process h t ω).mp hω
    _ ≤ _ := prob_exists_admissibleTuple_bad_le process.trials δ hD hh ht hδ
      process.trialsCount_le process.pointCap (fun x => process.point_survival_ge x)

theorem DeletionProcess.prob_not_goodTuples (process : DeletionProcess F D δ)
    (h t : ℕ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) :
    process.law.prob (fun ω => ¬ GoodTuples process h t ω) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  calc
    _ ≤ process.law.prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple process.shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) := by
      apply process.law.prob_mono
      intro ω hω
      exact (not_goodTuples_iff process h t ω).mp hω
    _ ≤ _ := prob_exists_admissibleTuple_bad_le_card_bound process.trials δ
      hD hh ht hδ process.trialsCount_le process.pointCap
      (fun x => process.point_survival_ge x)

namespace GoodTuples

variable {process : DeletionProcess F D δ} {h t : ℕ} {ω : process.Config}

theorem clean_crosscard_ge (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L) :
    δ * (t : ℝ) ^ 2 / 2 ≤
      ((process.survivorSet ω ∩ crossPoints a).card : ℝ) := by
  have heq := survivors_ignore_tuple_eq ω a
    (fun i => cleanLines_not_selected (hclean i))
  have hbound := hgood a ha
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors (tupleShapes a) ω ∩ crossPoints a).card : ℝ) at hbound
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors ∅ ω ∩ crossPoints a).card : ℝ)
  rw [heq] at hbound
  exact hbound

theorem no_sparse_clean_tuple (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L)
    (hsmall : ((process.survivorSet ω ∩ crossPoints a).card : ℝ) <
      δ * (t : ℝ) ^ 2 / 2) : False :=
  (not_lt_of_ge (hgood.clean_crosscard_ge L a ha hclean)) hsmall

end GoodTuples

end RyserCoveringCounterexample.LineCover

end

end OAI
