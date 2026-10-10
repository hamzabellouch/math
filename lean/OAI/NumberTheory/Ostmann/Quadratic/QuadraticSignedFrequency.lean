import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernels

namespace OAI

/-! # Signed odd-squarefree coordinates for nonzero Poisson frequencies -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_squarefree_odd_factor {q : ℕ} (hq : Squarefree q) :
    ∃ d b : ℕ, (d = 1 ∨ d = 2) ∧ Odd b ∧ Squarefree b ∧ q = d * b := by
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨b, hb⟩ := he
    have heq : q = 2 * b := by omega
    have hs : Squarefree (2 * b) := heq ▸ hq
    have hh := Nat.squarefree_mul_iff.mp hs
    exact ⟨2, b, Or.inr rfl, Nat.coprime_two_left.mp hh.1, hh.2.2, heq⟩
  · exact ⟨1, q, Or.inl rfl, ho, hq, (one_mul q).symm⟩

 theorem quadratic_signed_frequency_coordinates {H : ℕ} {h : ℤ}
    (hh : h ≠ 0) (hH : h.natAbs ≤ H) :
    ∃ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∃ c ∈ Finset.Icc 1 H,
      ∃ b ∈ oddSquarefreeRange H, h = a * (c : ℤ) ^ 2 * (b : ℤ) := by
  have habs : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  obtain ⟨q, c, hq, hc, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos habs
  obtain ⟨d, b, hd, hbo, hbs, hdb⟩ := quadratic_squarefree_odd_factor hsf
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hbpos : 0 < b := Nat.pos_of_ne_zero hbs.ne_zero
  have hcH : c ≤ H := by
    apply le_trans _ hH
    have hmul : c ^ 2 ≤ c ^ 2 * q := Nat.le_mul_of_pos_right _ hq
    rw [he] at hmul
    nlinarith
  have hbH : b ≤ H := by
    apply le_trans _ hH
    calc
      b ≤ d * b := Nat.le_mul_of_pos_left _ hdpos
      _ = q := hdb.symm
      _ ≤ c ^ 2 * q := Nat.le_mul_of_pos_left _ (pow_pos hc _)
      _ = _ := he
  have hcMem : c ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hc, hcH⟩
  have hbMem : b ∈ oddSquarefreeRange H :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbpos, hbH⟩, hbo, hbs⟩
  have heZ : (d : ℤ) * (c : ℤ) ^ 2 * (b : ℤ) = (h.natAbs : ℤ) := by
    have hn : d * c ^ 2 * b = h.natAbs := by rw [← he, hdb]; ring
    exact_mod_cast hn
  by_cases hs : 0 ≤ h
  · refine ⟨d, ?_, c, hcMem, b, hbMem, ?_⟩
    · rcases hd with rfl | rfl <;> simp
    · rw [heZ, Int.natCast_natAbs, abs_of_nonneg hs]
  · refine ⟨-(d : ℤ), ?_, c, hcMem, b, hbMem, ?_⟩
    · rcases hd with rfl | rfl <;> simp
    · rw [neg_mul, neg_mul, heZ, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hs), neg_neg]

noncomputable def quadraticFrequencyTriples (H : ℕ) : Finset ((ℤ × ℕ) × ℕ) :=
  ((({1, -1, 2, -2} : Finset ℤ).product (Finset.Icc 1 H)).product
    (oddSquarefreeRange H)).filter fun z =>
      (z.1.1 * (z.1.2 : ℤ) ^ 2 * (z.2 : ℤ)).natAbs ≤ H

noncomputable def quadraticNonzeroFrequencies (H : ℕ) : Finset ℤ :=
  (Finset.Icc (-(H : ℤ)) H).erase 0

 theorem quadratic_frequency_image (H : ℕ) :
    (quadraticFrequencyTriples H).image (fun z => z.1.1 * (z.1.2 : ℤ) ^ 2 * (z.2 : ℤ)) =
      quadraticNonzeroFrequencies H := by
  ext h
  constructor
  · intro hh
    obtain ⟨⟨⟨a, c⟩, b⟩, hz, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hz, hbound⟩ := Finset.mem_filter.mp hz
    obtain ⟨hac, hb⟩ := Finset.mem_product.mp hz
    obtain ⟨ha, hc⟩ := Finset.mem_product.mp hac
    have ha0 : a ≠ 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> norm_num
    have hc0 : (c : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hc).1)
    have hb0 : (b : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1)
    apply Finset.mem_erase.mpr
    refine ⟨mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero _ hc0)) hb0, ?_⟩
    apply Finset.mem_Icc.mpr
    have hh : |a * (c : ℤ) ^ 2 * (b : ℤ)| ≤ (H : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hbound
    exact abs_le.mp hh
  · intro hh
    obtain ⟨hh, hi⟩ := Finset.mem_erase.mp hh
    have hbound : h.natAbs ≤ H := by
      have hh := abs_le.mpr (Finset.mem_Icc.mp hi)
      rw [← Int.natCast_natAbs] at hh
      exact_mod_cast hh
    obtain ⟨a, ha, c, hc, b, hb, he⟩ := quadratic_signed_frequency_coordinates hh hbound
    apply Finset.mem_image.mpr
    refine ⟨((a, c), b), Finset.mem_filter.mpr ⟨?_, ?_⟩, he.symm⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hc⟩, hb⟩
    · simpa only [← he] using hbound

 theorem quadratic_nonzero_frequency_sum_le (H : ℕ) (F : ℤ → ℝ)
    (hF : ∀ h, 0 ≤ F h) :
    (∑ h ∈ quadraticNonzeroFrequencies H, F h) ≤
      ∑ z ∈ quadraticFrequencyTriples H, F (z.1.1 * (z.1.2 : ℤ) ^ 2 * (z.2 : ℤ)) := by
  rw [← quadratic_frequency_image]
  exact Finset.sum_image_le_of_nonneg (fun h _ => hF h)

end Ostmann

end OAI
