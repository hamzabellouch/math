import OAI.NumberTheory.JointDickman.Probability.RamanujanResidueFactor
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Exact enumeration of the lifts of reduced coefficient arcs -/

namespace JointDickman
open Finset

theorem val_finEquiv (q : ℕ) [NeZero q] (r : Fin q) :
    (ZMod.finEquiv q r).val = r.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

noncomputable def arcLiftEquiv (j q : ℕ) [NeZero (j*q)] :
    Fin j × Fin q ≃ ZMod (j*q) :=
  finProdFinEquiv.trans (ZMod.finEquiv (j*q)).toEquiv

theorem arcLiftEquiv_val {j q : ℕ} [NeZero (j*q)] (t : Fin j) (r : Fin q) :
    (arcLiftEquiv j q (t,r)).val = r.val+q*t.val := by
  exact val_finEquiv (j*q) (finProdFinEquiv (t,r))

theorem arcLiftEquiv_coprime {j q : ℕ} [NeZero (j*q)] (t : Fin j) (r : Fin q) :
    (arcLiftEquiv j q (t,r)).val.Coprime q ↔ r.val.Coprime q := by
  rw [arcLiftEquiv_val,← ZMod.coprime_mod_iff_coprime]
  simp [Nat.add_mod,Nat.mod_eq_of_lt r.isLt]

/-- Each reduced coefficient fraction has exactly j lifts, without a coprimality
assumption between j and q. -/
theorem reducedArc_lift_count (j q : ℕ) [NeZero j] [NeZero q] [NeZero (j*q)] :
    (∑ h : ZMod (j*q), if h.val.Coprime q then (1 : ℝ) else 0) = (j : ℝ)*q.totient := by
  classical
  have hqcount : (∑ r : Fin q, if r.val.Coprime q then (1 : ℝ) else 0) = q.totient := by
    rw [← coprime_residue_count q]
    apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
    intro r
    change (if r.val.Coprime q then (1 : ℝ) else 0) =
      if (ZMod.finEquiv q r).val.Coprime q then 1 else 0
    rw [val_finEquiv]
  calc
    _ = ∑ x : Fin j × Fin q, if x.2.val.Coprime q then (1 : ℝ) else 0 := by
      symm
      apply Fintype.sum_equiv (arcLiftEquiv j q)
      rintro ⟨t,r⟩
      simp only [arcLiftEquiv_coprime t r]
    _ = _ := by simp only [Fintype.sum_prod_type,hqcount,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem arcLiftEquiv_location {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (t : Fin j) (r : Fin q) :
    ((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ) =
      ((r.val : ℝ)/q+t.val)/j := by
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [arcLiftEquiv_val]
  push_cast
  field_simp

end JointDickman

end OAI
