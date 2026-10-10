import OAI.Analysis.KadisonKastler.AmplifiedAlgebra
import OAI.Analysis.FactorGeneration.MatrixUnits

namespace OAI

/-! # Finite full matrix algebras from countable matrix units

The finite algebras need not be increasing. Their matrix units agree with
the countable matrix units on any fixed finite collection of columns once
the matrix size is large enough.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def CuntzFamily.matrixUnits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : CuntzFamily ι H) : Generator.MatrixUnitSystem ι (H →L[ℂ] H) where
  entry i j := S.entry i * star (S.entry j)
  star_entry i j := by simp only [star_mul, star_star]
  mul_entry i j k l := by
    calc
      _ = S.entry i * (star (S.entry j) * S.entry k) * star (S.entry l) := by
        simp only [mul_assoc]
      _ = _ := by rw [S.orthogonal]; split_ifs <;> simp
  total := S.total

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

def periodicMatrixUnits (n : ℕ) [NeZero n] :
    Generator.MatrixUnitSystem (Fin n) (H →L[ℂ] H) :=
  (F.finiteCuntz n).matrixUnits

theorem periodicMatrixUnits_mem (n : ℕ) [NeZero n] (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i j : Fin n) :
    (F.periodicMatrixUnits n).entry i j ∈ M :=
  M.mul_mem (F.finiteCuntz_mem n M hM i)
    (star_mem (s := M.toStarSubalgebra) (F.finiteCuntz_mem n M hM j))

theorem finiteCuntz_column (n : ℕ) [NeZero n] (i : Fin n) (k : ℕ) (x : E) :
    (F.finiteCuntz n).entry i (F.column k x) = F.column (k * n + i) x :=
  F.regroupingOperator_column _ i k x

theorem finiteCuntz_adjoint_column (n : ℕ) [NeZero n] (i j : Fin n) (k : ℕ) (x : E) :
    star ((F.finiteCuntz n).entry i) (F.column (k * n + j) x) =
      if i = j then F.column k x else 0 :=
  F.adjoint_regrouping_column _ i j k x

theorem periodicMatrixUnits_column (n : ℕ) [NeZero n] (i j k : Fin n) (x : E) :
    (F.periodicMatrixUnits n).entry i j (F.column k x) =
      if j = k then F.column i x else 0 := by
  change (F.finiteCuntz n).entry i
    (star ((F.finiteCuntz n).entry j) (F.column k x)) = _
  have he := F.finiteCuntz_adjoint_column n j k 0 x
  simp only [Nat.zero_mul, Nat.zero_add] at he
  rw [he]
  split_ifs <;> simp only [map_zero, F.finiteCuntz_column, Nat.zero_mul, Nat.zero_add]

theorem periodicMatrixUnits_agree_on_column (n : ℕ) [NeZero n]
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) (x : E) :
    (F.periodicMatrixUnits n).entry ⟨i, hi⟩ ⟨j, hj⟩ (F.column k x) =
      F.entry i j (F.column k x) := by
  rw [F.entry_column]
  simpa only [Fin.mk.injEq] using
    F.periodicMatrixUnits_column n ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ x

end FullMatrixCorner

end

end KadisonKastler

end OAI
