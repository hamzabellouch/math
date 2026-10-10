import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMerge

namespace OAI

/-! The merged tape has one strictly ordered edge per occurring vertex pair,
and its coefficients grow by at most the original edge count. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

def supportIndex (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    Fin (support n xs).length := ⟨i.val,by simpa only [value,List.length_map] using i.isLt⟩

theorem value_pair (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    (((value n xs).get i).1, ((value n xs).get i).2.1) =
      (support n xs).get (supportIndex n xs i) := by
  exact congrArg (fun e : Bond => (e.1,e.2.1)) (value_get n xs i)

theorem value_pair_injective (n : ℕ) (xs : List Bond) :
    Function.Injective (fun i : Fin (value n xs).length =>
      (((value n xs).get i).1,((value n xs).get i).2.1)) := by
  intro i j h
  have hp := (value_pair n xs i).symm.trans (h.trans (value_pair n xs j))
  exact Fin.ext (congrArg (fun k : Fin (support n xs).length => k.val)
    ((support_nodup n xs).injective_get hp))

theorem value_ordered {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) : ∀ e ∈ value n xs, e.1<e.2.1 := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨b,hb,hbp⟩ := List.mem_map.mp hm
  subst p
  exact min_lt_max.mpr (h b hb)

theorem value_simple {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) (i j : Fin (value n xs).length) (hij : i≠j) :
    ¬(((value n xs).get i).1=((value n xs).get j).1 ∧
      ((value n xs).get i).2.1=((value n xs).get j).2.1) ∧
    ¬(((value n xs).get i).1=((value n xs).get j).2.1 ∧
      ((value n xs).get i).2.1=((value n xs).get j).1) := by
  constructor
  · rintro ⟨hl,hr⟩
    exact hij (value_pair_injective n xs (Prod.ext hl hr))
  · rintro ⟨hl,hr⟩
    have hi := value_ordered h _ (List.get_mem _ i)
    have hj := value_ordered h _ (List.get_mem _ j)
    omega

theorem weight_abs_le (xs : List Bond) (p : Pair) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ e ∈ xs, |(e.2.2:ℝ)| ≤ L) :
    |(weight xs p:ℝ)| ≤ xs.length*L := by
  induction xs with
  | nil => simp [weight]
  | cons e xs ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hone : |((if ordered e=p then e.2.2 else 0:ℚ):ℝ)| ≤ L := by
      by_cases hp : ordered e=p
      · simpa only [ite_eq_left hp] using he
      · simpa only [ite_eq_right hp,Rat.cast_zero,abs_zero] using hL
    change |(((if ordered e=p then e.2.2 else 0:ℚ)+weight xs p:ℚ):ℝ)| ≤ _
    rw [Rat.cast_add]
    have ha := abs_add_le ((if ordered e=p then e.2.2 else 0:ℚ):ℝ) (weight xs p:ℝ)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

end ContinuumCoulomb.QuantumListMerge

end

end OAI
