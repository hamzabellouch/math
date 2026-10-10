import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseRealExpectation

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def fair : SparseIntegerLaw (Fin 2) where
  length := 2
  states := Vector.ofFn id
  law := {
    denominator := 2
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

def mix (μ ν : SparseIntegerLaw α) : SparseIntegerLaw α :=
  fair.bindIndexed (fun a => if a.val=0 then μ else ν)

theorem mix_length (μ ν : SparseIntegerLaw α) : (mix μ ν).length=μ.length+ν.length := by
  change (∑ a : Fin 2, (if a.val=0 then μ else ν).length)=_
  norm_num [Fin.sum_univ_two]

theorem mix_moment (μ ν : SparseIntegerLaw α) (f : α → ℚ) :
    (mix μ ν).moment f=(1/2)*μ.moment f+(1/2)*ν.moment f := by
  rw [mix,bindIndexed_moment]
  change (∑ a : Fin 2, (1/2:ℚ)*(if a.val=0 then μ else ν).moment f)=_
  norm_num [Fin.sum_univ_two]

theorem expectation_mix (μ ν : SparseIntegerLaw α) (f : α → ℝ) :
    (mix μ ν).expectation f=(1/2)*μ.expectation f+(1/2)*ν.expectation f := by
  rw [mix,expectation_bindIndexed]
  change (∑ a : Fin 2, ((1/2:ℚ):ℝ)*(if a.val=0 then μ else ν).expectation f)=_
  norm_num [Fin.sum_univ_two]

theorem mix_property (μ ν : SparseIntegerLaw α) (P : α → Prop)
    (hμ : ∀ i : Fin μ.length, P μ.states[i.val])
    (hν : ∀ i : Fin ν.length, P ν.states[i.val]) :
    ∀ i : Fin (mix μ ν).length, P (mix μ ν).states[i.val] := by
  unfold mix
  apply bindIndexed_property
  intro a
  let Q : SparseIntegerLaw α → Prop := fun ρ => ∀ b : Fin ρ.length, P ρ.states[b.val]
  change Q (if a.val=0 then μ else ν)
  split_ifs
  · exact hμ
  · exact hν

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

theorem prob_mix [Fintype α] [DecidableEq α] (μ ν : SparseIntegerLaw α)
    (P : α → Prop) [DecidablePred P] :
    (mix μ ν).real.prob P=(1/2)*μ.real.prob P+(1/2)*ν.real.prob P := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_mix]

theorem prob_map [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : SparseIntegerLaw α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    (μ.map f).real.prob P=μ.real.prob (fun a => P (f a)) := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_map]

end MetricKMedian.SparseIntegerLaw

end OAI
