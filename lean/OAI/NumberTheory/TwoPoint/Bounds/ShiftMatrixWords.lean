import OAI.NumberTheory.TwoPoint.Bounds.MatrixClosedWords

namespace OAI

/-! Expand finite shift matrices using step labels, without enumerating intermediate sites. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {V E S : Type*} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def shiftMatrix (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) : Matrix V V ℝ := by
  classical
  exact fun i j => ∑ e, if next e (embed i) = embed j then weight e (embed i) else 0

noncomputable def retainedShiftWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (e : E) (x : S) : ℝ := by
  classical
  exact if next e x ∈ Set.range embed then weight e x else 0

omit [DecidableEq V] [Fintype E] in
lemma retainedShiftWeight_nonzero (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (e : E) (x : S)
    (hw : retainedShiftWeight embed next weight e x ≠ 0) :
    next e x ∈ Set.range embed ∧ weight e x ≠ 0 := by
  classical
  unfold retainedShiftWeight at hw
  split_ifs at hw with he
  · exact ⟨he, hw⟩
  · contradiction

def shiftWordEnd (next : E → S → S) : {k : ℕ} → S → (Fin k → E) → S
  | 0, x, _ => x
  | _k + 1, x, w => shiftWordEnd next (next (w 0) x) (Fin.tail w)

noncomputable def shiftWordWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) : {k : ℕ} → S → (Fin k → E) → ℝ
  | 0, _, _ => 1
  | _k + 1, x, w => retainedShiftWeight embed next weight (w 0) x *
      shiftWordWeight embed next weight (next (w 0) x) (Fin.tail w)

noncomputable def shiftWordTerm (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x y : S) (w : Fin k → E) : ℝ := by
  classical
  exact if shiftWordEnd next x w = y then shiftWordWeight embed next weight x w else 0

omit [DecidableEq V] [Fintype E] in
lemma sum_at_injective_site (embed : V → S) (hinj : Function.Injective embed)
    (z : S) (f : S → ℝ) :
    (∑ j, if z = embed j then f (embed j) else 0) =
      if z ∈ Set.range embed then f z else 0 := by
  classical
  by_cases hz : z ∈ Set.range embed
  · obtain ⟨j, rfl⟩ := hz
    have he (i : V) : embed j = embed i ↔ j = i := hinj.eq_iff
    simp [he]
  · have he (j : V) : z ≠ embed j := fun h => hz ⟨j, h.symm⟩
    simp [he, hz]

omit [DecidableEq V] in
lemma shiftMatrix_action (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (i : V) (f : S → ℝ) :
    (∑ j, shiftMatrix embed next weight i j * f (embed j)) =
      ∑ e, retainedShiftWeight embed next weight e (embed i) * f (next e (embed i)) := by
  classical
  simp only [shiftMatrix, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  have he (j : V) :
      (if next e (embed i) = embed j then weight e (embed i) else 0) * f (embed j) =
        if next e (embed i) = embed j then weight e (embed i) * f (embed j) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [sum_at_injective_site embed hinj (next e (embed i))
    (fun z => weight e (embed i) * f z)]
  unfold retainedShiftWeight
  split_ifs <;> simp

omit [DecidableEq V] [Fintype E] in
lemma shiftWordTerm_cons (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x y : S) (e : E) (w : Fin k → E) :
    shiftWordTerm embed next weight x y (Fin.cons e w) =
      retainedShiftWeight embed next weight e x *
        shiftWordTerm embed next weight (next e x) y w := by
  classical
  simp only [shiftWordTerm, shiftWordEnd, shiftWordWeight, Fin.cons_zero, Fin.tail_cons]
  split_ifs <;> simp

/-- Only the initial site and the step labels are summed. Intermediate sites
are forced by the integer shifts and killed when they leave the finite domain. -/
theorem shiftMatrix_pow_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) (i j : V) :
    (shiftMatrix embed next weight ^ k) i j =
      ∑ w : Fin k → E, shiftWordTerm embed next weight (embed i) (embed j) w := by
  classical
  induction k generalizing i with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, shiftWordTerm, shiftWordEnd, shiftWordWeight,
        hinj.eq_iff, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        pow_zero, one_smul]
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp_rw [ih]
      rw [shiftMatrix_action embed hinj next weight i
        (fun x => ∑ w : Fin k → E, shiftWordTerm embed next weight x (embed j) w)]
      rw [sum_fin_cons]
      simp_rw [mul_sum, shiftWordTerm_cons]

theorem shiftMatrix_power_closed_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) :
    matrixFrobeniusSq (shiftMatrix embed next weight ^ k) =
      ∑ i, ∑ j, ∑ u : Fin k → E, ∑ v : Fin k → E,
        shiftWordTerm embed next weight (embed i) (embed j) u *
          shiftWordTerm embed next weight (embed i) (embed j) v := by
  unfold matrixFrobeniusSq
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [shiftMatrix_pow_words embed hinj, pow_two, sum_mul]
  simp_rw [mul_sum]

omit [DecidableEq V] [Fintype E] in
lemma shiftWordWeight_support (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x : S) (w : Fin k → E)
    (hx : x ∈ Set.range embed) (hw : shiftWordWeight embed next weight x w ≠ 0) :
    shiftWordEnd next x w ∈ Set.range embed := by
  classical
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have hn : next (w 0) x ∈ Set.range embed := by
        by_contra hn
        exact hp.1 (by simp [retainedShiftWeight, hn])
      exact ih (next (w 0) x) (Fin.tail w) hn hp.2

omit [DecidableEq V] [Fintype E] in
/-- The common endpoint is forced by the first word, and hence contributes
no additional factor equal to the number of sites. -/
lemma sum_shiftWordTerm_pair (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) {k : ℕ} (i : V)
    (u v : Fin k → E) :
    (∑ j, shiftWordTerm embed next weight (embed i) (embed j) u *
      shiftWordTerm embed next weight (embed i) (embed j) v) =
      if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
        shiftWordWeight embed next weight (embed i) u *
          shiftWordWeight embed next weight (embed i) v else 0 := by
  classical
  by_cases he : shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v
  · have ht (j : V) : shiftWordTerm embed next weight (embed i) (embed j) u *
        shiftWordTerm embed next weight (embed i) (embed j) v =
        if shiftWordEnd next (embed i) u = embed j then
          shiftWordWeight embed next weight (embed i) u *
            shiftWordWeight embed next weight (embed i) v else 0 := by
      simp only [shiftWordTerm, ← he]
      split_ifs <;> simp
    simp_rw [ht]
    rw [sum_at_injective_site embed hinj _ (fun _ =>
      shiftWordWeight embed next weight (embed i) u *
        shiftWordWeight embed next weight (embed i) v)]
    by_cases hm : shiftWordEnd next (embed i) u ∈ Set.range embed
    · rw [ite_eq_left hm, ite_eq_left he]
    · have hz : shiftWordWeight embed next weight (embed i) u = 0 := by
        by_contra hz
        exact hm (shiftWordWeight_support embed next weight (embed i) u ⟨i, rfl⟩ hz)
      rw [ite_eq_right hm, ite_eq_left he, hz, zero_mul]
  · have ht (j : V) : shiftWordTerm embed next weight (embed i) (embed j) u *
        shiftWordTerm embed next weight (embed i) (embed j) v = 0 := by
      unfold shiftWordTerm
      split_ifs with hu hv
      · exact (he (hu.trans hv.symm)).elim
      all_goals simp
    simp [ht, he]

theorem shiftMatrix_moment_forced_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) :
    matrixFrobeniusSq (shiftMatrix embed next weight ^ k) =
      ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
          shiftWordWeight embed next weight (embed i) u *
            shiftWordWeight embed next weight (embed i) v else 0 := by
  classical
  rw [shiftMatrix_power_closed_words embed hinj]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  exact sum_shiftWordTerm_pair embed hinj next weight i u v

end TwoPointCorrelations

end OAI
