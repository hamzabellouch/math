import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedPreparation

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def outside (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseStarActivation.upper (point z.1 e)

def nominalCount (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseBernoulli.flag z.2.2 e

def raw (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ) (z : State n m) : ℚ :=
  ∑ e, (c e*outside b z e-(((D e).card:ℚ)*(b e:ℚ)+(z.2.1 e).card))

def BudgetSpec (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (t : ℚ) (z : State n m) : Prop :=
  (∀ e, z.2.1 e ⊆ D e) ∧
  (∀ e, outside b z e=(b e:ℚ) ∨ outside b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e=(b e:ℚ) ∨ nominalCount b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e ≤ outside b z e) ∧
  (∀ e i, (b e:ℚ)+(if i∈z.2.1 e then 1 else 0) ≤ outside b z e) ∧
  raw D c b z ≤ t

theorem kernel_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (q : Vector ℚ m) (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hsmall : (fractional q).card ≤ 1) :
    ∀ a : Fin (kernel D q hq).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point q e))+2)
        (kernel D q hq).states[a.val] := by
  unfold kernel
  apply SparseIntegerLaw.prod_property (SparseStarActivation.law D (point q))
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))
    (BudgetSpec D c b _)
  intro a d
  dsimp only [BudgetSpec]
  refine ⟨fun e => (SparseStarActivation.columns D (point q) hq a e).1,?_,?_,?_,?_,?_⟩
  · intro e
    dsimp only [outside,SparseStarActivation.upper]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,SparseBernoulli.flag]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,outside]
    rw [add_le_add_iff_left]
    by_cases he : 0 < point q e
    · simp only [SparseStarActivation.upper,ite_eq_left he,SparseBernoulli.flag]
      split_ifs <;> norm_num
    · have hz : point q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
      have hh := SparseBernoulli.fixed (point q) hq d e (Or.inl hz)
      rw [hh,hz]
      simp only [SparseStarActivation.upper,lt_self_iff_false,ite_false,le_refl]
  · intro e i
    dsimp only [outside]
    rw [add_le_add_iff_left]
    exact SparseStarActivation.upper_domination D (point q) hq a e i
  · have hh := SparseStarActivation.error D (point q) c hq hc hsmall a
    have he : raw D c b (q,(SparseStarActivation.law D (point q)).states[a.val],
        (SparseBernoulli.run (d := 2) (point q) hq m).states[d.val])=
        (∑ e, signed D c e*((b e:ℚ)+point q e))+
        ∑ e, (c e*(SparseStarActivation.upper (point q e)-point q e)+
          ((D e).card:ℚ)*point q e-
          (((SparseStarActivation.law D (point q)).states[a.val] e).card:ℚ)) := by
      unfold raw
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro e _
      dsimp only [raw,outside,signed]
      ring
    rw [he]
    linarith only [hh]

theorem law_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (p : Vector ℚ m) (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    ∀ a : Fin (law D c p hp hc).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point p e))+3)
        (law D c p hp hc).states[a.val] := by
  unfold law
  apply SparseIntegerLaw.bindIndexed_property _ _ (BudgetSpec D c b _)
  intro a d
  let hu : ∀ e, 0 < signed D c e → signed D c e ≤ 1 := fun e _ =>
    (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2
  have ha := SparseSignedRounding.round_invariants (signed D c) p hp hu a
  have hh := kernel_budget D c b (SparseSignedRounding.round (signed D c) p hp).states[a.val]
    ha.1 hc ha.2.1 d
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,?_⟩
  have hb : (∑ e, signed D c e*((b e:ℚ)+point (SparseSignedRounding.round (signed D c) p hp).states[a.val] e)) ≤
      (∑ e, signed D c e*((b e:ℚ)+point p e))+1 := by
    simp only [mul_add,sum_add_distrib]
    linarith only [ha.2.2]
  exact hh.2.2.2.2.2.trans (by linarith only [hb])

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
