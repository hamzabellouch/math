import OAI.Probability.DilutedSpin.MatrixRoot
import OAI.Probability.DilutedSpin.ProfileHistory

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance shapeMatrixPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N k : ℕ}

noncomputable def matrixSplitTest (T : PrescribedTree L) (q : C → T.Leaf)
    (B : C → C → ℕ) : ℝ := if ∀ a b, B a b = splitDepth T (q a) (q b) then 1 else 0

noncomputable def spatialProduct (D : C → FinitePath Ω L → Fin N → ℝ)
    (x : C → FinitePath Ω L) : ℝ := (∑ i, ∏ c, D c (x c) i)/(N:ℝ)

omit [Fintype Ω] [DecidableEq C] in
lemma spatialProduct_bound [Fintype Ω] [DecidableEq C]
    (D : C → FinitePath Ω L → Fin N → ℝ)
    (hD : ∀ c x i, |D c x i| ≤ 1) (x : C → FinitePath Ω L) :
    |spatialProduct D x| ≤ 1 := by
  unfold spatialProduct
  simp only [abs_div, Nat.abs_cast]
  have hs : |∑ i : Fin N, ∏ c, D c (x c) i| ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i : Fin N, |∏ c, D c (x c) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun c _ => hD c _ i))
      _ = _ := by simp
  by_cases hN : N = 0
  · subst N; simp
  · exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr (by simpa using hs)

lemma matrixObservableHistory_sum {ι : Type} (I : Finset ι)
    (T : PrescribedTree L) (q : C → T.Leaf) (K : KernelTower Ω L) (m : Fin (L+1) → ℝ)
    (cs : List C) (S : PrescribedTree L) (a : S.Leaf)
    (A : ι → (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m cs S a (fun x => ∑ i ∈ I, A i x) f =
      ∑ i ∈ I, matrixObservableHistory T q K m cs S a (A i) f := by
  unfold matrixObservableHistory weightedMatrixHistory
  dsimp only
  rw [← labeledHistory_sum]
  congr 1
  funext R pos g
  split_ifs with h
  · simp only [Finset.mul_sum,FiniteLaw.expect_sum]
  · simp only [Finset.sum_const_zero]

lemma matrixObservableHistory_div
    (T : PrescribedTree L) (q : C → T.Leaf) (K : KernelTower Ω L) (m : Fin (L+1) → ℝ)
    (cs : List C) (S : PrescribedTree L) (a : S.Leaf)
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (c : ℝ) :
    matrixObservableHistory T q K m cs S a (fun x => A x/c) f =
      matrixObservableHistory T q K m cs S a A f/c := by
  unfold matrixObservableHistory weightedMatrixHistory
  rw [div_eq_mul_inv,mul_comm,← labeledHistory_mul_left]
  congr 1
  funext R pos g
  split_ifs with h
  · dsimp only
    simp only [div_eq_mul_inv, mul_comm _ c⁻¹, mul_left_comm _ c⁻¹, FiniteLaw.expect_mul_left]
  · simp only [mul_zero]

lemma shapeHistory_matrix (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    shapeHistory K m (matrixSplitTest T q) D S a f =
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
      (fun x => ∏ c, D c (x c)) f := by
  unfold shapeHistory matrixObservableHistory weightedMatrixHistory
  congr 1
  funext R pos g
  unfold matrixSplitTest
  split_ifs <;> simp

/-- Empirical multioverlap and literal full-matrix history commute with the
single shared site average. Old tests may depend on every old sample. -/
theorem matrix_history_spatialProduct (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : Option (Fin k) → FinitePath Ω (L+1) → Fin N → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a (spatialProduct D) f =
      (∑ i : Fin N, shapeHistory K m (matrixSplitTest T q) (fun c x => D c x i) S a f)/(N:ℝ) := by
  unfold spatialProduct
  rw [matrixObservableHistory_div,matrixObservableHistory_sum]
  simp_rw [shapeHistory_matrix]

lemma matrix_history_spatialProduct_same (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : FinitePath Ω (L+1) → Fin N → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a (spatialProduct (fun _ => D)) f =
      (∑ i : Fin N, shapeHistory K m (matrixSplitTest T q)
        (fun c x => match c with | none => if true = true then D x i else 1 | some _ => D x i) S a f)/(N:ℝ) := by
  rw [matrix_history_spatialProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext c x
  cases c <;> rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
