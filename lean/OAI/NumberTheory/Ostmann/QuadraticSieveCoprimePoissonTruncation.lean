import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonLatticeBounds

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

noncomputable def nonzeroIntegerCutoff (L : ℝ) : Finset ℤ :=
  (Finset.Icc ⌈-L⌉ ⌊L⌋).erase 0

@[simp] theorem mem_nonzeroIntegerCutoff (L : ℝ) (n : ℤ) :
    n ∈ nonzeroIntegerCutoff L ↔ n ≠ 0 ∧ |(n : ℝ)| ≤ L := by
  simp only [nonzeroIntegerCutoff, Finset.mem_erase, Finset.mem_Icc, Int.ceil_le,
    Int.le_floor, abs_le]

theorem tsum_eq_zero_add_trunc_add_tail (f : ℤ → ℂ) (hf : Summable f)
    (L : ℝ) (hL : 0 ≤ L) :
    (∑' n : ℤ, f n) = f 0 + (∑ n ∈ nonzeroIntegerCutoff L, f n) +
      (∑' n : ℤ, if L < |(n : ℝ)| then f n else 0) := by
  classical
  let g : ℤ → ℂ := fun n => if n ∈ nonzeroIntegerCutoff L then f n else 0
  let h : ℤ → ℂ := fun n => if L < |(n : ℝ)| then f n else 0
  have hg : Summable g :=
    (hf.indicator (nonzeroIntegerCutoff L : Set ℤ)).congr (fun n => by simp [g, Set.indicator_apply])
  have hh : Summable h :=
    (hf.indicator {n : ℤ | L < |(n : ℝ)|}).congr (fun n => by simp [h, Set.indicator_apply])
  have heq (n : ℤ) : f n = (if n = 0 then f 0 else 0) + g n + h n := by
    by_cases hn : n = 0
    · subst n
      simp [g, h, not_lt_of_ge hL]
    · by_cases hcut : |(n : ℝ)| ≤ L
      · simp [g, h, hn, hcut, not_lt_of_ge hcut]
      · simp [g, h, hn, hcut, lt_of_not_ge hcut]
  have hsingle : Summable (fun n : ℤ => if n = 0 then f 0 else 0) := (hasSum_ite_eq 0 (f 0)).summable
  rw [tsum_congr heq, (hsingle.add hg).tsum_add hh, hsingle.tsum_add hg]
  simp only [tsum_ite_eq]
  congr 2
  calc
    (∑' n : ℤ, g n) = ∑ n ∈ nonzeroIntegerCutoff L, g n :=
      tsum_eq_sum (fun n hn => by simp only [g, ite_eq_right hn])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [g, ite_eq_left hn]

theorem schwartz_fourier_zero_eq_integral (ψ : 𝓢(ℝ, ℂ)) : 𝓕 ψ (0 : ℝ) = ∫ x : ℝ, ψ x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

theorem schwartz_lattice_eq_zero_add_nonzero (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ψ ((n : ℝ) * y)) = ψ 0 + nonzeroLattice ψ y := by
  have hf : Summable (fun n : ℤ => ψ ((n : ℝ) * y)) := by
    simpa only [dilatedSchwartz_apply, mul_comm] using
      schwartz_summable_int (dilatedSchwartz y hy.ne' ψ)
  simpa only [Int.cast_zero, zero_mul, nonzeroLattice] using hf.tsum_eq_add_tsum_ite 0

theorem schwartz_poisson_scaled_truncated (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (L : ℝ) (hL : 0 ≤ L) :
    (∑' n : ℤ, ψ ((n : ℝ) / X)) =
      (X : ℂ) * ((∫ x : ℝ, ψ x) +
        (∑ l ∈ nonzeroIntegerCutoff L, 𝓕 ψ ((l : ℝ) * X)) + latticeTail (𝓕 ψ) X L) := by
  rw [schwartz_poisson_scaled ψ X hX]
  congr 1
  have hf : Summable (fun l : ℤ => 𝓕 ψ ((l : ℝ) * X)) := by
    simpa only [dilatedSchwartz_apply, mul_comm] using
      schwartz_summable_int (dilatedSchwartz X hX.ne' (𝓕 ψ))
  simpa only [Int.cast_zero, zero_mul, schwartz_fourier_zero_eq_integral, latticeTail] using
    tsum_eq_zero_add_trunc_add_tail _ hf L hL

end Ostmann.QuadraticSieve

end OAI
