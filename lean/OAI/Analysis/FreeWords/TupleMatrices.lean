import Mathlib
import OAI.Analysis.FreeWords.OperatorRows
import OAI.Analysis.FreeWords.TupleCombinatorics

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable [Fintype α] [DecidableEq α]

def tupleScalarMatrix (p q : ℕ) (W : Multiset α)
    (a : Fin q → α) (b : Fin p → α) : E →L[ℂ] E :=
  if tupleLabels a + tupleLabels b = W then 1 else 0

omit [CompleteSpace E] in
theorem tupleScalarMatrix_bound (p q : ℕ) (W : Multiset α) :
    MatrixSqBound (tupleScalarMatrix (E := E) p q W)
      ((p.factorial : ℝ) * q.factorial) := by
  let w (a : Fin q → α) (b : Fin p → α) : ℝ :=
    if tupleLabels a + tupleLabels b = W then 1 else 0
  have hr a : ∑ b, w a b ≤ (p.factorial : ℝ) := by
    simpa only [w, Finset.sum_boole] using
      (Nat.cast_le (α := ℝ)).mpr (tuple_completion_card p (tupleLabels a) W)
  have hc b : ∑ a, w a b ≤ (q.factorial : ℝ) := by
    simpa only [w, add_comm (tupleLabels _) (tupleLabels b), Finset.sum_boole] using
      (Nat.cast_le (α := ℝ)).mpr (tuple_completion_card q (tupleLabels b) W)
  have h := scalar_matrix_bound (E := E) w (fun a b => by dsimp [w]; split_ifs <;> positivity)
    _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr hc
  convert h using 1
  funext a b
  dsimp only [tupleScalarMatrix, w]
  split_ifs <;> simp

def tupleProjectionMatrix (P : α → E →L[ℂ] E) (p q : ℕ) (W : Multiset α)
    (a : Fin q → α) (b : Fin p → α) : E →L[ℂ] E :=
  ∑ c, if tupleLabels a + {c} + tupleLabels b = W then P c else 0

def tupleMissingWeight (p q : ℕ) (W : Multiset α)
    (a : Fin q → α) (b : Fin p → α) : ℝ :=
  ((Finset.univ.filter (fun c => tupleLabels a + {c} + tupleLabels b = W)).card : ℝ)

theorem tupleProjectionMatrix_bound (P : α → E →L[ℂ] E)
    (hP : ∀ c, IsStarProjection (P c))
    (horth : ∀ c e, c ≠ e → P c * P e = 0) (hsum : ∑ c, P c = 1)
    (p q : ℕ) (W : Multiset α) :
    MatrixSqBound (tupleProjectionMatrix P p q W)
      ((p.factorial : ℝ) * q.factorial) := by
  let s (a : Fin q → α) (c : α) :=
    Finset.univ.filter (fun b : Fin p → α => tupleLabels a + {c} + tupleLabels b = W)
  have hr a c : (s a c).card ≤ p.factorial :=
    tuple_completion_card p (tupleLabels a + {c}) W
  have hc b c : (Finset.univ.filter (fun a => b ∈ s a c)).card ≤ q.factorial := by
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and,
      show ∀ a : Fin q → α, tupleLabels a + {c} + tupleLabels b =
        tupleLabels b + {c} + tupleLabels a from fun a => by ac_rfl] using
      tuple_completion_card q (tupleLabels b + {c}) W
  have h := projection_incidence_bound P hP horth hsum s _ _ hr hc
  convert h using 1
  funext a b
  simp only [tupleProjectionMatrix, s, Finset.mem_filter, Finset.mem_univ, true_and]

theorem tupleMissingWeight_rows (p q : ℕ) (W : Multiset α) (a : Fin q → α) :
    (∑ b, tupleMissingWeight p q W a b) ≤ ((p+1).factorial : ℝ) := by
  dsimp only [tupleMissingWeight]
  exact_mod_cast sum_card_tuple_completion p (tupleLabels a) W

theorem tupleMissingWeight_cols (p q : ℕ) (W : Multiset α) (b : Fin p → α) :
    (∑ a, tupleMissingWeight p q W a b) ≤ ((q+1).factorial : ℝ) := by
  have h := tupleMissingWeight_rows (α := α) q p W b
  have he (a : Fin q → α) (c : α) : tupleLabels b + {c} + tupleLabels a =
      tupleLabels a + {c} + tupleLabels b := by ac_rfl
  simpa only [tupleMissingWeight, he] using h

omit [CompleteSpace E] in
theorem tupleMissingMatrix_bound (p q : ℕ) (W : Multiset α) :
    MatrixSqBound (fun a b => (tupleMissingWeight p q W a b : ℂ) • (1 : E →L[ℂ] E))
      (((p+1).factorial : ℝ) * (q+1).factorial) := by
  apply scalar_matrix_bound _ (fun _ _ => Nat.cast_nonneg _) _ _
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact tupleMissingWeight_rows p q W
  · exact tupleMissingWeight_cols p q W

def tuplePresMatrix (P : α → E →L[ℂ] E) (Q : E →L[ℂ] E) (z : ℂ)
    (p q : ℕ) (W : Multiset α) (a : Fin q → α) (b : Fin p → α) : E →L[ℂ] E :=
  ∑ c, if tupleLabels a + {c} + tupleLabels b = W then Q * (P c - z • 1) * Q else 0

omit [CompleteSpace E] in
theorem tuplePresMatrix_eq (P : α → E →L[ℂ] E) (Q : E →L[ℂ] E) (z : ℂ)
    (p q : ℕ) (W : Multiset α) (a : Fin q → α) (b : Fin p → α) :
    tuplePresMatrix P Q z p q W a b =
      Q * (tupleProjectionMatrix P p q W a b +
        (-z) • ((tupleMissingWeight p q W a b : ℂ) • 1)) * Q := by
  have hcount : ((tupleMissingWeight p q W a b : ℂ) • (1 : E →L[ℂ] E)) =
      ∑ c, if tupleLabels a + {c} + tupleLabels b = W then 1 else 0 := by
    simp only [tupleMissingWeight, Complex.ofReal_natCast, ← Finset.sum_filter,
      Finset.sum_const, Nat.cast_smul_eq_nsmul]
  rw [hcount]
  simp only [tuplePresMatrix, tupleProjectionMatrix, Finset.smul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> simp [sub_eq_add_neg]

theorem tuplePresMatrix_bound (P : α → E →L[ℂ] E)
    (hP : ∀ c, IsStarProjection (P c))
    (horth : ∀ c e, c ≠ e → P c * P e = 0) (hsum : ∑ c, P c = 1)
    (Q : E →L[ℂ] E) (hQ : ‖Q‖ ≤ 1) (z : ℂ)
    (p q : ℕ) (W : Multiset α) :
    MatrixSqBound (tuplePresMatrix P Q z p q W)
      ((Real.sqrt ((p.factorial : ℝ) * q.factorial) +
        ‖z‖ * Real.sqrt (((p+1).factorial : ℝ) * (q+1).factorial)) ^ 2) := by
  have hpq : 0 ≤ (p.factorial : ℝ) * q.factorial := by positivity
  have hpq' : 0 ≤ ((p+1).factorial : ℝ) * (q+1).factorial := by positivity
  have hPmat : MatrixSqBound (tupleProjectionMatrix P p q W)
      ((Real.sqrt ((p.factorial : ℝ) * q.factorial)) ^ 2) := by
    rw [Real.sq_sqrt hpq]
    exact tupleProjectionMatrix_bound P hP horth hsum p q W
  have hSmat : MatrixSqBound
      (fun a b => (-z) • ((tupleMissingWeight p q W a b : ℂ) • (1 : E →L[ℂ] E)))
      ((‖z‖ * Real.sqrt (((p+1).factorial : ℝ) * (q+1).factorial)) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hpq']
    simpa only [norm_neg] using (tupleMissingMatrix_bound (E := E) p q W).smul (-z)
  have h := (hPmat.add hSmat (Real.sqrt_nonneg _)
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).compress (sq_nonneg _) Q hQ
  convert h using 1
  funext a b
  exact tuplePresMatrix_eq P Q z p q W a b

end

end KKFreeWords
end

end OAI
