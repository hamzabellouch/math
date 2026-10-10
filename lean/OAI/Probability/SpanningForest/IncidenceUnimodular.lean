import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Incidence

variable {V E : Type*} [DecidableEq V]

def signedIncidence (src dst : E → V) : Matrix V E ℝ :=
  fun v e => (if v = src e then 1 else 0) - (if v = dst e then 1 else 0)

lemma sum_endpoint_indicator {n : ℕ} (f : Fin n → V)
    (hf : Function.Injective f) (v : V) :
    (∑ i, if f i = v then (1 : ℝ) else 0) =
      if ∃ i, f i = v then 1 else 0 := by
  classical
  by_cases hv : ∃ i, f i = v
  · obtain ⟨i, rfl⟩ := hv
    simp [hf.eq_iff]
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hv ⟨i, hi⟩)

lemma incidence_column_sum {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E) :
    (∑ i, signedIncidence src dst (f i) e) =
      (if ∃ i, f i = src e then 1 else 0) -
      (if ∃ i, f i = dst e then 1 else 0) := by
  simp only [signedIncidence, Finset.sum_sub_distrib,
    sum_endpoint_indicator f hf]

lemma incidence_source_only {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E)
    (i : Fin n) (hsrc : f i = src e) (hdst : ¬ ∃ k, f k = dst e) :
    (fun k => signedIncidence src dst (f k) e) = Pi.single i 1 := by
  ext k
  have hkd : f k ≠ dst e := fun hk => hdst ⟨k, hk⟩
  simp [signedIncidence, ← hsrc, hf.eq_iff, hkd, Pi.single_apply]

lemma incidence_target_only {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E)
    (i : Fin n) (hdst : f i = dst e) (hsrc : ¬ ∃ k, f k = src e) :
    (fun k => signedIncidence src dst (f k) e) = Pi.single i (-1) := by
  ext k
  have hks : f k ≠ src e := fun hk => hsrc ⟨k, hk⟩
  simp [signedIncidence, ← hdst, hf.eq_iff, hks, Pi.single_apply]
  split_ifs <;> norm_num

theorem signedIncidence_minor_mem_sign (src dst : E → V) (n : ℕ)
    (f : Fin n → V) (g : Fin n → E) (hf : Function.Injective f) :
    ((signedIncidence src dst).submatrix f g).det ∈ Set.range SignType.cast := by
  classical
  induction n with
  | zero =>
      exact ⟨1, by simp⟩
  | succ n ih =>
      let A := (signedIncidence src dst).submatrix f g
      by_cases hsplit : ∃ j,
          ((∃ i, f i = src (g j)) ∧ ¬ ∃ i, f i = dst (g j)) ∨
          ((∃ i, f i = dst (g j)) ∧ ¬ ∃ i, f i = src (g j))
      · obtain ⟨j, hj⟩ := hsplit
        have hsingle : ∃ i : Fin (n + 1), ∃ s : SignType,
            (fun k => A k j) = Pi.single i (s.cast : ℝ) := by
          rcases hj with ⟨⟨i, hi⟩, hother⟩ | ⟨⟨i, hi⟩, hother⟩
          · exact ⟨i, 1, incidence_source_only src dst f hf (g j) i hi hother⟩
          · refine ⟨i, -1, ?_⟩
            simpa [A] using incidence_target_only src dst f hf (g j) i hi hother
        obtain ⟨i, s, hs⟩ := hsingle
        have hdet := Matrix.det_succ_column A j
        rw [Fintype.sum_eq_single i] at hdet
        · have hii : A i j = s.cast := by
            simpa using congrFun hs i
          rw [hii] at hdet
          change A.det ∈ Set.range SignType.cast
          rw [hdet]
          change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
          refine mul_mem (mul_mem ?_ (Set.mem_range_self s)) ?_
          · apply pow_mem
            exact ⟨-1, by simp⟩
          · exact ih (f ∘ i.succAbove) (g ∘ j.succAbove)
              (hf.comp Fin.succAbove_right_injective)
        · intro k hki
          have hkj : A k j = 0 := by
            simpa [Pi.single_eq_of_ne hki] using congrFun hs k
          simp [hkj]
      · have hsum : ∀ j : Fin (n + 1), ∑ i, A i j = 0 := by
          intro j
          have hiff : (∃ i, f i = src (g j)) ↔ (∃ i, f i = dst (g j)) := by
            constructor
            · intro h
              by_contra hn
              exact hsplit ⟨j, Or.inl ⟨h, hn⟩⟩
            · intro h
              by_contra hn
              exact hsplit ⟨j, Or.inr ⟨h, hn⟩⟩
          change (∑ i, signedIncidence src dst (f i) (g j)) = 0
          rw [incidence_column_sum src dst f hf]
          simp only [hiff, sub_self]
        have hdet : A.det = 0 := by
          rw [Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
            A 0 0 (fun j _ => hsum j), hsum 0, mul_zero, zero_mul]
        exact ⟨0, by simpa using hdet.symm⟩

theorem signedIncidence_isTotallyUnimodular (src dst : E → V) :
    (signedIncidence src dst).IsTotallyUnimodular := by
  intro n f g hf _
  exact signedIncidence_minor_mem_sign src dst n f g hf

theorem signedIncidence_submatrix_det_mem_sign {ι : Type*}
    [Fintype ι] [DecidableEq ι] (src dst : E → V)
    (f : ι → V) (g : ι → E) :
    ((signedIncidence src dst).submatrix f g).det ∈ Set.range SignType.cast := by
  exact (Matrix.isTotallyUnimodular_iff_fintype _).mp
    (signedIncidence_isTotallyUnimodular src dst) ι f g

theorem signedIncidence_det_sq_eq_one_of_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (src dst : E → V)
    (f : ι → V) (g : ι → E)
    (hdet : ((signedIncidence src dst).submatrix f g).det ≠ 0) :
    (((signedIncidence src dst).submatrix f g).det)^2 = 1 := by
  obtain ⟨s, hs⟩ := signedIncidence_submatrix_det_mem_sign src dst f g
  rw [← hs] at hdet ⊢
  cases s with
  | zero => exact (hdet rfl).elim
  | neg => norm_num [SignType.cast]
  | pos => norm_num [SignType.cast]

theorem signedIncidence_det_sq_eq_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι] (src dst : E → V)
    (f : ι → V) (g : ι → E) :
    (((signedIncidence src dst).submatrix f g).det)^2 =
      if ((signedIncidence src dst).submatrix f g).det = 0 then 0 else 1 := by
  classical
  by_cases hd : ((signedIncidence src dst).submatrix f g).det = 0
  · simp [hd]
  · simp [hd, signedIncidence_det_sq_eq_one_of_ne_zero src dst f g hd]

end Problem336.Incidence

end

end OAI
