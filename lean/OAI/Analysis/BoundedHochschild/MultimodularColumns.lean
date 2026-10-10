import OAI.Analysis.BoundedHochschild.CompletelyBoundedLastSlices

namespace OAI

/-! The algebraic column identity for a cochain that is multimodular over
a star subalgebra. This is the matrix estimate used in the properly infinite
reduction; all module identities are the usual adjacent-input identities. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

structure MultimodularOver (R : StarSubalgebra ℂ M) {n : ℕ}
    (f : Cochain M (n + 1)) : Prop where
  left : ∀ (r : M), r ∈ R → ∀ x,
    f (Function.update x 0 (r * x 0)) = r * f x
  right : ∀ (r : M), r ∈ R → ∀ x,
    f (Function.update x (Fin.last n) (x (Fin.last n) * r)) = f x * r
  balance : ∀ (r : M), r ∈ R → ∀ x (j : Fin n),
    f (Function.update x j.castSucc (x j.castSucc * r)) =
      f (Function.update x j.succ (r * x j.succ))

def shiftedColumnTuple {n : ℕ} (a b : Fin (n + 1) → M) (r : M)
    (k : Fin (n + 1)) : Fin (n + 1) → M :=
  fun j => if j < k then b j else if j = k then r * a j else a j

lemma shiftedColumnTuple_zero {n : ℕ} (a b : Fin (n + 1) → M) (r : M) :
    shiftedColumnTuple a b r 0 = Function.update a 0 (r * a 0) := by
  ext j
  by_cases hj : j = 0
  · subst j; simp [shiftedColumnTuple]
  · simp [shiftedColumnTuple, hj]

lemma multimodular_slide_column {R : StarSubalgebra ℂ M} {n : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (r : M) (hr : r ∈ R) (a b : Fin (n + 1) → M)
    (hb : ∀ j : Fin n, b j.castSucc * r = r * a j.castSucc)
    (k : Fin (n + 1)) : f (shiftedColumnTuple a b r k) = r * f a := by
  induction k using Fin.induction with
  | zero => rw [shiftedColumnTuple_zero]; exact hf.left r hr a
  | succ k ih =>
      let x : Fin (n + 1) → M := fun j => if j ≤ k.castSucc then b j else a j
      have h₀ : shiftedColumnTuple a b r k.castSucc =
          Function.update x k.castSucc (x k.castSucc * r) := by
        ext j
        by_cases he : j = k.castSucc
        · subst j
          simp [shiftedColumnTuple, x, hb k]
        · by_cases hj : j < k.castSucc
          · simp [shiftedColumnTuple, x, he, hj, le_of_lt hj]
          · have hle : ¬j ≤ k.castSucc := fun h => he (le_antisymm h (le_of_not_gt hj))
            simp [shiftedColumnTuple, x, he, hj, hle]
      have h₁ : shiftedColumnTuple a b r k.succ =
          Function.update x k.succ (r * x k.succ) := by
        ext j
        by_cases he : j = k.succ
        · subst j
          have hnot : ¬ k.succ ≤ k.castSucc := by simp [Fin.le_def]
          simp [shiftedColumnTuple, x, hnot]
        · have he' : j < k.succ ↔ j ≤ k.castSucc := by
            simp only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
            omega
          simp [shiftedColumnTuple, x, he, he']
      rw [h₁, ← hf.balance r hr x k, ← h₀]
      exact ih

def columnDiagonal {m : ℕ} (c : Fin m → PartialIso M) (a : M) : M :=
  ∑ i, (c i : M) * a * star (c i : M)

lemma columnDiagonal_mul_column {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (a : M) (j : Fin m) : columnDiagonal c a * (c j : M) = (c j : M) * a := by
  classical
  simp only [columnDiagonal, Finset.sum_mul, mul_assoc]
  simp [column_star_mul c hi ho]

lemma multimodular_column_term {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hc : ∀ i, (c i : M) ∈ R) (a : Fin n → M) (y : M) (i j : Fin m) :
    f (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y * star (c j : M))) =
      (c i : M) * f (Fin.snoc a y) * star (c j : M) := by
  have he : Function.update (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y) :
      Fin (n + 1) → M) (Fin.last n) (((c i : M) * y) * star (c j : M)) =
      Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y * star (c j : M)) := by
    ext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  have hright := hf.right (star (c j : M)) (star_mem (hc j))
    (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y))
  rw [Fin.snoc_last, he] at hright
  rw [hright]
  congr 1
  have h := multimodular_slide_column f hf (c i : M) (hc i)
    (Fin.snoc a y) (Fin.snoc (fun k => columnDiagonal c (a k)) y)
    (fun k => by simpa using columnDiagonal_mul_column c hi ho (a k) i) (Fin.last n)
  convert h using 2
  ext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [shiftedColumnTuple]
  · have hlt : k.castSucc < Fin.last n := by simp [Fin.lt_def]
    simp [shiftedColumnTuple, hlt]

end BoundedHochschild.KadisonRingrose

end

end OAI
