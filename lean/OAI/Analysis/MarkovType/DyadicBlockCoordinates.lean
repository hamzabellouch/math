import OAI.Analysis.MarkovType.FiniteDyadicProbability
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def dyadicBlockEquiv (m N : ℕ) : DyadicWord (m * N) ≃ (Fin m → DyadicWord N) where
  toFun ω b i := ω (finProdFinEquiv (b, i))
  invFun f j := f ((finProdFinEquiv (m := m) (n := N)).symm j).1
    ((finProdFinEquiv (m := m) (n := N)).symm j).2
  left_inv ω := by
    funext j
    exact congrArg ω ((finProdFinEquiv (m := m) (n := N)).apply_symm_apply j)
  right_inv f := by
    funext b i
    exact congrArg (fun z : Fin m × Fin N => f z.1 z.2)
      ((finProdFinEquiv (m := m) (n := N)).symm_apply_apply (b, i))

@[simp] theorem dyadicBlockEquiv_apply {m N : ℕ} (ω : DyadicWord (m * N))
    (b : Fin m) (i : Fin N) :
    dyadicBlockEquiv m N ω b i = ω (finProdFinEquiv (b, i)) := rfl

@[simp] theorem dyadicBlockEquiv_symm_apply {m N : ℕ}
    (f : Fin m → DyadicWord N) (j : Fin (m * N)) :
    (dyadicBlockEquiv m N).symm f j =
      f ((finProdFinEquiv (m := m) (n := N)).symm j).1
        ((finProdFinEquiv (m := m) (n := N)).symm j).2 := rfl

theorem dyadicBlockIndex_val {m N : ℕ} (b : Fin m) (i : Fin N) :
    (finProdFinEquiv (b, i)).val = i.val + N * b.val := rfl

theorem dyadicBlockIndex_symm_val {m N : ℕ} (j : Fin (m * N)) :
    ((finProdFinEquiv (m := m) (n := N)).symm j).2.val +
      N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val = j.val :=
  congrArg Fin.val ((finProdFinEquiv (m := m) (n := N)).apply_symm_apply j)

theorem dyadicBlock_mass (m N : ℕ) (ω : DyadicWord (m * N)) :
    (dyadicLaw (m * N)).mass ω =
      ((dyadicLaw N).independentCopies m).mass (dyadicBlockEquiv m N ω) := by
  rw [dyadicLaw_mass, FiniteLaw.independentCopies_mass]
  simp only [dyadicLaw_mass, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

theorem dyadicBlock_prob (m N : ℕ) (A : (Fin m → DyadicWord N) → Prop) :
    (dyadicLaw (m * N)).prob (fun ω => A (dyadicBlockEquiv m N ω)) =
      ((dyadicLaw N).independentCopies m).prob A := by
  classical
  unfold FiniteLaw.prob
  simp_rw [dyadicBlock_mass m N]
  exact (dyadicBlockEquiv m N).sum_comp
    (fun x => if A x then ((dyadicLaw N).independentCopies m).mass x else 0)

theorem dyadicBlock_expect (m N : ℕ) (f : (Fin m → DyadicWord N) → ℝ) :
    (dyadicLaw (m * N)).expect (fun ω => f (dyadicBlockEquiv m N ω)) =
      ((dyadicLaw N).independentCopies m).expect f := by
  unfold FiniteLaw.expect
  simp_rw [dyadicBlock_mass m N]
  exact (dyadicBlockEquiv m N).sum_comp
    (fun x => ((dyadicLaw N).independentCopies m).mass x * f x)

theorem dyadicBlock_prob_coord {m N : ℕ} (b : Fin m) (A : DyadicWord N → Prop) :
    (dyadicLaw (m * N)).prob (fun ω => A (dyadicBlockEquiv m N ω b)) =
      (dyadicLaw N).prob A :=
  (dyadicBlock_prob m N (fun x => A (x b))).trans
    ((dyadicLaw N).independentCopies_prob_coord b A)

theorem dyadicBlock_expect_coord {m N : ℕ} (b : Fin m) (f : DyadicWord N → ℝ) :
    (dyadicLaw (m * N)).expect (fun ω => f (dyadicBlockEquiv m N ω b)) =
      (dyadicLaw N).expect f :=
  (dyadicBlock_expect m N (fun x => f (x b))).trans
    ((dyadicLaw N).independentCopies_expect_coord b f)

def dyadicBlockPrefix {m N : ℕ} (j : Fin (m * N)) (α : DyadicWord j.val) :
    DyadicWord (((finProdFinEquiv (m := m) (n := N)).symm j).2.val) :=
  fun k => α ⟨k.val + N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val, by
    calc
      k.val + N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val <
          ((finProdFinEquiv (m := m) (n := N)).symm j).2.val +
            N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val :=
        Nat.add_lt_add_right k.is_lt _
      _ = j.val := dyadicBlockIndex_symm_val j⟩

theorem dyadicBlockPrefix_prefix {m N : ℕ} (j : Fin (m * N))
    (ω : DyadicWord (m * N)) :
    dyadicBlockPrefix j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt)) =
      dyadicPrefix (dyadicBlockEquiv m N ω
        ((finProdFinEquiv (m := m) (n := N)).symm j).1)
        ((finProdFinEquiv (m := m) (n := N)).symm j).2.val
        (Nat.le_of_lt ((finProdFinEquiv (m := m) (n := N)).symm j).2.is_lt) := by
  funext k
  apply congrArg ω
  apply Fin.ext
  rfl

end MarkovSuperreflexivity

end

end OAI
