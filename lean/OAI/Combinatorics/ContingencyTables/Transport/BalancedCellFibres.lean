import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalLargeProfiles
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! # Exact one-cell fibres of the physical balanced profile sum -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical

variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev Profiles (M : C → ℕ) := (c : C) → Fin (M c+1)
abbrev Others (M : C → ℕ) (t : C) := (c : {c : C // c≠t}) → Fin (M c.val+1)

def profile (M : C → ℕ) (a : Profiles M) : C×Bool → ℕ :=
  fun p => if p.2 then M p.1-(a p.1).val else (a p.1).val

noncomputable def fibre (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (k : Fin (M t+1)) : ℝ :=
  ∑ a : Profiles M,if a t=k then F (profile M a) else 0

noncomputable def join (M : C → ℕ) (t : C)
    (k : Fin (M t+1)) (a : Others M t) : Profiles M :=
  (Equiv.piSplitAt t (fun c => Fin (M c+1))).symm (k,a)

omit [Fintype C] in
lemma join_at (M : C → ℕ) (t : C) (k : Fin (M t+1)) (a : Others M t) :
    join M t k a t=k := by
  exact congrArg Prod.fst ((Equiv.piSplitAt t (fun c => Fin (M c+1))).apply_symm_apply (k,a))

omit [Fintype C] in
lemma join_other (M : C → ℕ) (t : C) (k : Fin (M t+1)) (a : Others M t)
    (c : {c : C // c≠t}) : join M t k a c.val=a c := by
  exact congrFun (congrArg Prod.snd
    ((Equiv.piSplitAt t (fun c => Fin (M c+1))).apply_symm_apply (k,a))) c

/-- The fibre has no multiplicity: choosing the retained cell fixes
that coordinate and leaves exactly the independent choices elsewhere. -/
theorem fibre_eq_sum (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (k : Fin (M t+1)) :
    fibre M F t k=∑ a : Others M t,F (profile M (join M t k a)) := by
  let e := Equiv.piSplitAt t (fun c => Fin (M c+1))
  have he : (∑ a : Profiles M,if a t=k then F (profile M a) else 0)=
      ∑ p : Fin (M t+1)×Others M t,if p.1=k then F (profile M (e.symm p)) else 0 := by
    apply Fintype.sum_equiv e
    intro a
    simp only [Equiv.symm_apply_apply]
    rfl
  unfold fibre
  rw [he,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

theorem fibre_nonnegative (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (hF : ∀ z,0 ≤ F z) (t : C) (k : Fin (M t+1)) : 0 ≤ fibre M F t k := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hF _
  · exact le_rfl

/-- The actual one-cell fibres partition the full physical finite sum. -/
theorem sum_fibre (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ) (t : C) :
    (∑ k : Fin (M t+1),fibre M F t k)=∑ a : Profiles M,F (profile M a) := by
  unfold fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

end ContingencyTables.BalancedCellFibres

end OAI
