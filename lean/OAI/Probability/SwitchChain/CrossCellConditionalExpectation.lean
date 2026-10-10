import OAI.Probability.SwitchChain.CrossCellMoments
import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

def firstPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.1)

def secondPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.2)

theorem expectation_factors_key
    {Ω κ : Type*} [Fintype Ω] (key : Ω → κ) (f : EuclideanSpace ℝ Ω) :
    ∃ g : κ → ℝ, PairFibers.expectation (Setoid.ker key) f =
      WithLp.toLp 2 (fun z => g (key z)) := by
  have hf : Function.FactorsThrough
      (fun z => PairFibers.expectation (Setoid.ker key) f z) key := by
    intro x y hxy
    exact PairFibers.expectation_constant (Setoid.ker key) f hxy
  obtain ⟨g,hg⟩ := (Function.factorsThrough_iff _).mp hf
  refine ⟨g, ?_⟩
  ext z
  exact congrFun hg z

theorem expectation_first_right_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) (z : Cell s r c) :
    PairFibers.expectation (firstPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.2)) z =
        conditionalRight s r c z.val.2.1 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (firstPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.1 = z.val.2.1) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.1 = w.val.2.1 ↔ w.val.2.1 = z.val.2.1
    exact eq_comm
  rw [hcell]
  rfl

theorem expectation_second_left_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : α → ℝ) (z : Cell s r c) :
    PairFibers.expectation (secondPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.1)) z =
        conditionalLeft s r c z.val.2.2 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (secondPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.2 = z.val.2.2) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.2 = w.val.2.2 ↔ w.val.2.2 = z.val.2.2
    exact eq_comm
  rw [hcell]
  rfl

end Problem315.CrossCellMoments

end

end OAI
