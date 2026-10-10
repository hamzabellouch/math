import OAI.NumberTheory.Ostmann.Quadratic.KernelPopulationBound

namespace OAI

/-! # The refined large-kernel discard estimate -/

namespace Ostmann

open scoped BigOperators Classical

/-- This is the population estimate used to discard kernels larger than H.
The denominator m occurs only through sqrt(m), uniformly over all kernels. -/
theorem exists_large_kernel_discard_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ) (X H : ℝ), 0 < m → 0 ≤ X → 0 < H →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      ((S.filter fun x => H < |(f x : ℝ)|).card : ℝ) ≤
        (S.image f).card * (C * (Real.sqrt (X / H) + Real.sqrt m)) := by
  obtain ⟨C, hC, hpop⟩ := exists_kernel_population_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro S f root m h X H hm hX hH hred hroot hspan
  let R := S.filter fun x => H < |(f x : ℝ)|
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hfiber (u : ℤ) (hu : u ∈ R.image f) :
      ((R.filter fun x => f x = u).card : ℝ) ≤ C * (Real.sqrt (X / H) + Real.sqrt m) := by
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    have hlarge : H < |(u : ℝ)| := by
      have hh := (Finset.mem_filter.mp hx).2
      rwa [hxu] at hh
    have hu0 : u ≠ 0 := by
      intro hu0
      simp only [hu0, Int.cast_zero, abs_zero] at hlarge
      linarith
    have hb := hpop (R.filter fun x => f x = u) root m h u X hm hu0 hred
      (by
        intro y hy
        obtain ⟨hy, heq⟩ := Finset.mem_filter.mp hy
        simpa only [heq] using hroot y (hRS hy))
      (by
        intro y hy z hz
        exact hspan y (hRS (Finset.mem_filter.mp hy).1) z (hRS (Finset.mem_filter.mp hz).1))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_left hX hH hlarge.le)) le_rfl
  have hc : (R.card : ℝ) ≤ (R.image f).card *
      (C * (Real.sqrt (X / H) + Real.sqrt m)) := by
    rw [Finset.card_eq_sum_card_image f R, Nat.cast_sum]
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (R.image f)
      (fun u => ((R.filter fun x => f x = u).card : ℝ)) _ hfiber
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.image_subset_image hRS)

end Ostmann

end OAI
