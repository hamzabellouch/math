import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace OAI

/-! # Equal finite blocks in an initial segment -/

namespace KadisonKastler

def finiteBlockIndex {k m : ℕ} (i : Fin k) : Fin (m / k) ↪ Fin m where
  toFun r := ⟨i.val * (m / k) + r.val, by
    calc
      i.val * (m / k) + r.val < i.val * (m / k) + m / k := Nat.add_lt_add_left r.isLt _
      _ = (i.val + 1) * (m / k) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * (m / k) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
      _ ≤ m := Nat.mul_div_le m k⟩
  inj' r s h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

def finiteBlockSet {k m : ℕ} (i : Fin k) : Finset (Fin m) :=
  Finset.univ.map (finiteBlockIndex (m := m) i)

@[simp] theorem finiteBlockSet_card {k m : ℕ} (i : Fin k) :
    (finiteBlockSet (m := m) i).card = m / k := by
  simp [finiteBlockSet]

theorem finiteBlockSet_disjoint {k m : ℕ} (i j : Fin k) (hij : i ≠ j) :
    Disjoint (finiteBlockSet (m := m) i) (finiteBlockSet (m := m) j) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp ha
  obtain ⟨s, _, hs⟩ := Finset.mem_map.mp hb
  have hpos : 0 < m / k := lt_of_le_of_lt (Nat.zero_le _) r.isLt
  have he : i.val * (m / k) + r.val = j.val * (m / k) + s.val :=
    congrArg Fin.val (hr.trans hs.symm)
  have hd := congrArg (fun n => n / (m / k)) he
  rw [Nat.mul_comm i.val, Nat.mul_comm j.val, Nat.mul_add_div hpos,
    Nat.mul_add_div hpos, Nat.div_eq_of_lt r.isLt, Nat.div_eq_of_lt s.isLt,
    Nat.add_zero, Nat.add_zero] at hd
  exact hij (Fin.ext hd)

end KadisonKastler

end OAI
