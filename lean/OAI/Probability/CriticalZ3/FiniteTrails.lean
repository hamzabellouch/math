import OAI.Probability.CriticalZ3.RelayProbability

namespace OAI

universe uD uV

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

/-! Finite balanced directed boundaries admit closed edge-simple trails.
This is used only for the planar contour dependency of the main proof. -/
open Classical Function
namespace FiniteTrails
variable {D : Type uD} {V : Type uV} [Fintype D]

noncomputable def successor (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v}) :
    Equiv.Perm D :=
  (Equiv.sigmaFiberEquiv head).symm.trans
    ((Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (hbal v))).trans
      (Equiv.sigmaFiberEquiv tail))

theorem successor_tail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (d : D) : tail (successor tail head hbal d) = head d := by
  exact (Fintype.equivOfCardEq (hbal (head d)) ⟨d,rfl⟩).property

/-- Some cycle class has nonzero weight whenever the total weight does. -/
theorem exists_cycle_nonzero (σ : Equiv.Perm D) (w : D → ℤ)
    (hw : ∑ d, w d ≠ 0) :
    ∃ d, (∑ e : D, if σ.SameCycle d e then w e else 0) ≠ 0 := by
  let Q := Quotient (Equiv.Perm.SameCycle.setoid σ)
  let q : D → Q := Quotient.mk _
  have hs : ∑ c : Q, (∑ e : D, if q e = c then w e else 0) = ∑ e, w e := by
    calc
      _ = ∑ e : D, ∑ c : Q, if q e = c then w e else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        exact (Finset.sum_ite_eq Finset.univ (q e) (fun _ => w e)).trans (ite_eq_left (Finset.mem_univ _))
  by_contra! h
  have hz : (∑ c : Q, ∑ e : D, if q e = c then w e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    obtain ⟨d,rfl⟩ := Quotient.exists_rep c
    convert h d using 1
    apply Finset.sum_congr rfl
    intro e _
    have he : q e = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) d ↔ σ.SameCycle d e := by
      rw [Quotient.eq]
      exact Equiv.Perm.sameCycle_comm
    simp only [he]
  exact hw (hs.symm.trans hz)

theorem period_pos (σ : Equiv.Perm D) (d : D) : 0 < minimalPeriod σ d :=
  minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d)

noncomputable def cycleEquiv (σ : Equiv.Perm D) (d : D) :
    Fin (minimalPeriod σ d) ≃ {e // σ.SameCycle d e} := by
  let f : Fin (minimalPeriod σ d) → {e // σ.SameCycle d e} := fun i =>
    ⟨σ^[i.val] d,by
      rw [←Equiv.Perm.coe_pow]
      exact Equiv.Perm.SameCycle.rfl.pow_right⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp (congrArg Subtype.val hij)
  · intro e
    obtain ⟨k,hk⟩ := e.property.exists_nat_pow_eq
    refine ⟨⟨k % minimalPeriod σ d,Nat.mod_lt _ (period_pos σ d)⟩,?_⟩
    apply Subtype.ext
    change σ^[k % minimalPeriod σ d] d = e.val
    rw [iterate_mod_minimalPeriod_eq,←Equiv.Perm.coe_pow]
    exact hk

def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩

/-- A closed trail has distinct edges and retains the nonzero marked crossing sum. -/
theorem exists_closed_trail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by
  let σ := successor tail head hbal
  obtain ⟨d,hd⟩ := exists_cycle_nonzero σ w hw
  let n := minimalPeriod σ d
  have hn : 0 < n := period_pos σ d
  let e : Fin n → D := fun i => σ^[i.val] d
  refine ⟨n,hn,e,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij
  · intro i
    have he : e (next hn i) = σ (e i) := by
      change σ^[(i.val+1)%n] d = σ (σ^[i.val] d)
      rw [iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
    rw [he]
    exact successor_tail tail head hbal (e i)
  · have hs := (cycleEquiv σ d).sum_comp (fun z : {e // σ.SameCycle d e} => w z.val)
    have ht : (∑ z : {e // σ.SameCycle d e}, w z.val) =
        ∑ e : D, if σ.SameCycle d e then w e else 0 := by
      rw [←Finset.sum_filter]; exact (Finset.sum_subtype _ (by simp) w).symm
    rw [ht] at hs
    exact hs.symm ▸ hd

end FiniteTrails

end OAI
