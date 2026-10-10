import OAI.Analysis.MassAction.Model

namespace OAI

universe uIota uJ

noncomputable section

namespace Problem326Aux

/-- A perturbation by less than half the absolute value preserves the sign
and leaves a quantitative gap from zero. -/
theorem sign_gap_of_abs_sub_lt {a b : ℝ}
    (h : |a - b| < |b| / 2) :
    (0 < b → 0 < a ∧ b / 2 < a) ∧
    (b < 0 → a < 0 ∧ a < b / 2) ∧ |b| / 2 < |a| := by
  have hsub := abs_lt.mp h
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [abs_of_neg hb] at hsub
    have ha : a < 0 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · intro hb'
      linarith
    · intro _
      exact ⟨ha, by linarith⟩
    · rw [abs_of_neg hb, abs_of_neg ha]
      linarith
  · subst b
    simp only [abs_zero, zero_div] at h
    exact False.elim (not_lt_of_ge (abs_nonneg _) h)
  · rw [abs_of_pos hb] at hsub
    have ha : 0 < a := by linarith
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact ⟨ha, by linarith⟩
    · intro hb'
      linarith
    · rw [abs_of_pos hb, abs_of_pos ha]
      linarith

/-- Bounding each coordinate perturbation bounds any finite scalar product. -/
theorem abs_sum_mul_le {ι : Type uIota} [Fintype ι]
    (p r v : ι → ℝ) (E : ℝ)
    (h : ∀ i, |p i - r i| ≤ E) :
    |∑ i, (p i - r i) * v i| ≤ E * ∑ i, |v i| := by
  calc
    |∑ i, (p i - r i) * v i| ≤ ∑ i, |(p i - r i) * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |p i - r i| * |v i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, E * |v i| := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
    _ = E * ∑ i, |v i| := (Finset.mul_sum _ _ _).symm

/-- Monomials at exponential coordinates have the expected scalar exponent. -/
theorem prod_rpow_pow_eq {ι : Type uIota} [Fintype ι]
    {h : ℝ} (hh : 0 < h) (p : ι → ℝ) (y : ι → ℕ) :
    (∏ i, (h ^ (p i)) ^ (y i)) = h ^ (∑ i, p i * (y i : ℝ)) := by
  rw [Real.rpow_sum_of_pos hh]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.rpow_mul_natCast hh.le (p i) (y i)).symm

/-- An exponent gap orders monomials quantitatively when the base is below one. -/
theorem prod_rpow_pow_le_of_gap {ι : Type uIota} [Fintype ι]
    {h H : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (p : ι → ℝ) (y z : ι → ℕ)
    (hgap : H ≤ ∑ i, p i * ((z i : ℝ) - (y i : ℝ))) :
    (∏ i, (h ^ (p i)) ^ (z i)) ≤
      h ^ H * (∏ i, (h ^ (p i)) ^ (y i)) := by
  rw [prod_rpow_pow_eq hh, prod_rpow_pow_eq hh, ← Real.rpow_add hh]
  apply Real.rpow_le_rpow_of_exponent_ge hh hh1
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib] at hgap
  linarith

/-- A finite collection of positive thresholds admits a common positive bound,
including when the indexing set is empty. -/
theorem exists_positive_common_bound {ι : Type uIota} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) {C : ℝ} (hC : 0 < C) :
    ∃ E : ℝ, 0 < E ∧ E ≤ C ∧ ∀ i ∈ s, E ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, hC, le_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨E, hE, hEC, hEf⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min E (f a), lt_min hE (hf a (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans hEC, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hEf i hi)

/-- One tolerance controls all nonzero pairings with finitely many directions.
No continuity of the eventual tolerance as a function of `r` is required. -/
theorem exists_pairing_tolerance {ι : Type uIota} {J : Type uJ} [Fintype ι] [Fintype J]
    (r : ι → ℝ) (v : J → ι → ℝ) :
    ∃ E : ℝ, 0 < E ∧ E ≤ 1 / 2 ∧
      ∀ p : ι → ℝ, (∀ i, |p i - r i| ≤ E) →
      ∀ j, (∑ i, r i * v j i) ≠ 0 →
        |(∑ i, p i * v j i) - (∑ i, r i * v j i)| <
          |∑ i, r i * v j i| / 2 := by
  classical
  have hlocal : ∀ j : J, ∃ e : ℝ, 0 < e ∧
      ((∑ i, r i * v j i) ≠ 0 →
        (∑ i, |v j i|) * e < |∑ i, r i * v j i| / 2) := by
    intro j
    by_cases hj : (∑ i, r i * v j i) = 0
    · exact ⟨1, zero_lt_one, fun h => (h hj).elim⟩
    · obtain ⟨e, he, he'⟩ := exists_pos_mul_lt
        (half_pos (abs_pos.mpr hj)) (∑ i, |v j i|)
      exact ⟨e, he, fun _ => he'⟩
  choose e he he' using hlocal
  obtain ⟨E, hE, hEhalf, hEe⟩ := exists_positive_common_bound
    Finset.univ e (fun j _ => he j) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨E, hE, hEhalf, ?_⟩
  intro p hp j hj
  calc
    |(∑ i, p i * v j i) - (∑ i, r i * v j i)| =
        |∑ i, (p i - r i) * v j i| := by
          rw [← Finset.sum_sub_distrib]
          simp_rw [sub_mul]
    _ ≤ E * ∑ i, |v j i| := abs_sum_mul_le p r (v j) E hp
    _ ≤ e j * ∑ i, |v j i| := mul_le_mul_of_nonneg_right
      (hEe j (Finset.mem_univ j)) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    _ < |∑ i, r i * v j i| / 2 := by simpa [mul_comm] using he' j hj

/-- Finite nonzero pairings have a positive common quantitative gap. -/
theorem exists_positive_pairing_gap {J : Type uJ} [Fintype J] (a : J → ℝ) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ j, a j ≠ 0 → H ≤ |a j| / 2 := by
  classical
  let f : J → ℝ := fun j => if a j = 0 then 1 else |a j| / 2
  have hf : ∀ j, 0 < f j := by
    intro j
    dsimp [f]
    split_ifs with hj
    · norm_num
    · exact half_pos (abs_pos.mpr hj)
  obtain ⟨H, hH, hH1, hHf⟩ := exists_positive_common_bound
    Finset.univ f (fun j _ => hf j) zero_lt_one
  refine ⟨H, hH, hH1, ?_⟩
  intro j hj
  simpa [f, hj] using hHf j (Finset.mem_univ j)

end Problem326Aux

namespace Problem326

/-- Exact mass-action monomial representation at exponential coordinates. -/
theorem monomial_rpow {d : ℕ} {h : ℝ} (hh : 0 < h)
    (p : Fin d → ℝ) (y : Fin d → ℕ) :
    monomial (fun i => h ^ p i) y = h ^ (∑ i, p i * (y i : ℝ)) :=
  Problem326Aux.prod_rpow_pow_eq hh p y

/-- Exact monomial-order interface for active-slope sign-gap arguments. -/
theorem monomial_le_rpow_mul_of_gap {d : ℕ} {h H : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (p : Fin d → ℝ) (y z : Fin d → ℕ)
    (hgap : H ≤ ∑ i, p i * ((z i : ℝ) - (y i : ℝ))) :
    monomial (fun i => h ^ p i) z ≤ h ^ H * monomial (fun i => h ^ p i) y :=
  Problem326Aux.prod_rpow_pow_le_of_gap hh hh1 p y z hgap

end Problem326

end

end OAI
