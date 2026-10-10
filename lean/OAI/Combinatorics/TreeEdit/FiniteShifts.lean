import OAI.Combinatorics.TreeEdit.FiniteTree
import OAI.Combinatorics.TreeEdit.WordOperations

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteTree

lemma w_period {m : ℕ} (p : ℕ → Fin m → ℕ) (h q : ℕ) : q • w p h q = 0 := by
  induction h generalizing q with
  | zero =>
    change q • (1 : ZMod q) = 0
    simp [nsmul_eq_mul]
  | succ h ih =>
    apply funext
    intro i
    change q • ((∏ j, p h j) • w p h (q * p h i)) = 0
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (p h) (Finset.mem_univ i)
    calc
      _ = c • ((q * p h i) • w p h (q * p h i)) := by
        simp only [← mul_smul, hc]
        congr 1
        ring
      _ = 0 := by rw [ih]; simp

lemma cycle_cost {m T h q s : ℕ} {p : ℕ → Fin m → ℕ} (hs : s ≤ T)
    (x : State m p (h + 1) q) :
    ed (word p T (h + 1) q x).val (word p T (h + 1) q (x + s • u p h q)).val ≤
      2 * s * (m * length m T h) := by
  apply Words.ed_cycles_shift hs
  intro a i
  apply congrArg (word p T h (q * p h i))
  change x i + (a.val + s) • w p h (q * p h i) =
    (x i + s • w p h (q * p h i)) + a.val • w p h (q * p h i)
  rw [add_nsmul]
  abel

noncomputable def embedChild {m : ℕ} (p : ℕ → Fin m → ℕ) (h q : ℕ) (i : Fin m) :
    State m p h (q * p h i) →+ State m p (h + 1) q :=
  AddMonoidHom.single (fun i => State m p h (q * p h i)) i

lemma child_cost {m T h q : ℕ} {p : ℕ → Fin m → ℕ} (i : Fin m)
    (z : State m p h (q * p h i)) (C : ℝ)
    (hC : ∀ y, (ed (word p T h (q * p h i) y).val
      (word p T h (q * p h i) (y + z)).val : ℝ) ≤ C)
    (x : State m p (h + 1) q) :
    (ed (word p T (h + 1) q x).val
      (word p T (h + 1) q (x + embedChild p h q i z)).val : ℝ) ≤ T * C := by
  classical
  have hh := Words.ed_cycles
    (fun (a : Fin T) j => word p T h (q * p h j) (x j + a.val • w p h (q * p h j)))
    (fun a j => word p T h (q * p h j) ((x + embedChild p h q i z) j + a.val • w p h (q * p h j)))
  have hh' : (ed (word p T (h + 1) q x).val
      (word p T (h + 1) q (x + embedChild p h q i z)).val : ℝ) ≤
    ∑ a : Fin T, ∑ j : Fin m, (ed
      (word p T h (q * p h j) (x j + a.val • w p h (q * p h j))).val
      (word p T h (q * p h j) ((x + embedChild p h q i z) j + a.val • w p h (q * p h j))).val : ℝ) := by
    exact_mod_cast hh
  apply hh'.trans
  calc
    _ ≤ ∑ _a : Fin T, C := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_eq_single i]
      · simp only [Pi.add_apply, embedChild, AddMonoidHom.single_apply, Pi.single_eq_same]
        change (ed (word p T h (q * p h i) (x i + a.val • w p h (q * p h i))).val
          (word p T h (q * p h i) ((x i + z) + a.val • w p h (q * p h i))).val : ℝ) ≤ C
        rw [add_right_comm (x i) z]
        exact hC _
      · intro j _ hji
        have he : embedChild p h q i z j = 0 := by simp [embedChild, hji]
        simp only [Pi.add_apply, he, add_zero, ed_self, Nat.cast_zero]
      · simp
    _ = T * C := by simp

end FiniteTree

end TreeEdit

end OAI
