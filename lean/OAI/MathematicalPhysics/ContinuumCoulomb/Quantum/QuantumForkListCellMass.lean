import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellLocality
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkCells

namespace OAI

/-! A literal fork round has bounded density in the original coarse cells.
The proof counts its actual fresh indices through the ordered pair catalog. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph
open scoped BigOperators Classical
variable {β : Type*} [DecidableEq β]

theorem next_cell_mass (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (p : β) :
    qmaCellMass (fun v : Fin (next N s).1 => nextCell s cell v.val) p =
      qmaCellMass (fun v : Fin s.1 => cell v.val) p+
      2*∑ e : Fin (pairCount s.2.2.2), if cell (localPair s.2.2.2 e).1.val=p then 1 else 0 := by
  unfold qmaCellMass
  change (∑ v : Fin (s.1+2*pairCount s.2.2.2), if nextCell s cell v.val=p then 1 else 0)=_
  rw [show s.1+2*pairCount s.2.2.2=s.1+pairCount s.2.2.2*2 by omega]
  rw [← (vertexEquiv s.1 (pairCount s.2.2.2)).sum_comp]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two]
  have ho (v : Fin s.1) :
      nextCell s cell (vertexEquiv s.1 (pairCount s.2.2.2) (Sum.inl v)).val=cell v.val := by
    change nextCell s cell (old s.1 (pairCount s.2.2.2) v).val=cell v.val
    simpa only [MediatorIteration.old_val] using nextCell_old s cell v.val v.isLt
  have hf (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
      nextCell s cell (vertexEquiv s.1 (pairCount s.2.2.2) (Sum.inr (e,b))).val=
        cell (localPair s.2.2.2 e).1.val := by
    change nextCell s cell (fresh s.1 (pairCount s.2.2.2) e b).val=_
    simpa only [MediatorIteration.fresh_val,Nat.mul_comm,actualSite,Matrix.cons_val_zero] using
      nextCell_fresh s hs cell e b
  simp_rw [ho,hf]
  rw [Finset.sum_add_distrib]
  omega

theorem pair_cell_mass_le (s : State) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D) (p : β) :
    (∑ e : Fin (pairCount s.2.2.2), if cell (localPair s.2.2.2 e).1.val=p then 1 else 0) ≤
      D*qmaCellMass (fun i : Fin s.2.2.2.length => cell i.val) p := by
  have he := (pairEquiv s.2.2.2).symm.sum_comp
    (fun q : LocalPair s.2.2.2 => if cell q.1.val=p then (1:ℕ) else 0)
  change (∑ e : Fin (pairCount s.2.2.2),
    (fun q : LocalPair s.2.2.2 => if cell q.1.val=p then (1:ℕ) else 0)
      ((pairEquiv s.2.2.2).symm e)) ≤ _
  rw [he]
  simp only [LocalPair,Fintype.sum_sigma,qmaCellMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : cell i.val=p
  · simp only [hi,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one]
    exact (Nat.div_le_self _ _).trans (hd i)
  · simp [hi]

theorem prefix_cell_mass_le (m n : ℕ) (h : m ≤ n) (cell : ℕ → β) (p : β) :
    qmaCellMass (fun i : Fin m => cell i.val) p ≤
      qmaCellMass (fun i : Fin n => cell i.val) p := by
  unfold qmaCellMass
  change (∑ i : Fin m, if cell i.val=p then 1 else 0) ≤
    ∑ i : Fin n, if cell i.val=p then 1 else 0
  calc
    _ = ∑ i ∈ Finset.range m, if cell i=p then 1 else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => if cell i=p then 1 else 0) m
    _ ≤ ∑ i ∈ Finset.range n, if cell i=p then 1 else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => Nat.zero_le _)
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i => if cell i=p then 1 else 0) n).symm

theorem next_cell_mass_le (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D) (p : β) :
    qmaCellMass (fun v : Fin (next N s).1 => nextCell s cell v.val) p ≤
      (1+2*D)*qmaCellMass (fun v : Fin s.1 => cell v.val) p := by
  rw [next_cell_mass s hs N cell p]
  have hp := pair_cell_mass_le s cell D hd p
  have hc := prefix_cell_mass_le s.2.2.2.length s.1 hs.centers cell p
  calc
    _ ≤ qmaCellMass (fun v : Fin s.1 => cell v.val) p+
        2*(D*qmaCellMass (fun i : Fin s.2.2.2.length => cell i.val) p) := by omega
    _ ≤ qmaCellMass (fun v : Fin s.1 => cell v.val) p+
        2*(D*qmaCellMass (fun i : Fin s.1 => cell i.val) p) := by gcongr
    _ = _ := by ring

theorem iterate_group_le (s : State) (N : ℚ) (k i : ℕ) (hi : i<s.2.2.2.length) :
    (groupAt (iterate N k s).2.2.2 i).length ≤ (groupAt s.2.2.2 i).length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterate,next_group_length N (iterate N k s) i (by rwa [iterate_centers])]
    omega

theorem iterate_cell_mass_le (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D)
    (k : ℕ) (p : β) :
    qmaCellMass (fun v : Fin (iterate N k s).1 => iterateCell N k s cell v.val) p ≤
      (1+2*D)^k*qmaCellMass (fun v : Fin s.1 => cell v.val) p := by
  induction k with
  | zero => simp only [iterate,iterateCell,pow_zero,one_mul,le_refl]
  | succ k ih =>
    have hd' : ∀ i : Fin (iterate N k s).2.2.2.length,
        (groupAt (iterate N k s).2.2.2 i.val).length ≤ D := by
      intro i
      have hi : i.val<s.2.2.2.length := by simpa only [iterate_centers] using i.isLt
      exact (iterate_group_le s N k i.val hi).trans (hd ⟨i.val,hi⟩)
    have hn := next_cell_mass_le (iterate N k s) (iterate_validPorts N s hs k)
      N (iterateCell N k s cell) D hd' p
    change qmaCellMass (fun v : Fin (next N (iterate N k s)).1 =>
      nextCell (iterate N k s) (iterateCell N k s cell) v.val) p ≤ _
    calc
      _ ≤ (1+2*D)*qmaCellMass (fun v : Fin (iterate N k s).1 =>
          iterateCell N k s cell v.val) p := hn
      _ ≤ (1+2*D)*((1+2*D)^k*qmaCellMass (fun v : Fin s.1 => cell v.val) p) :=
        Nat.mul_le_mul_left _ ih
      _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
