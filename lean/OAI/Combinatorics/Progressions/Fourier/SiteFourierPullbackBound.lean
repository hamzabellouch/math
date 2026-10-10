import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
import OAI.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem sitePullbackFrequency_bound {K S : Type*} [Fintype S] {m : ℕ}
    {J : Fin m → Type*} (site : S → K → ℤ) (b : ∀ j, Matrix S (J j) ℤ)
    {P B : ℝ} (hP : 0 ≤ P)
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (hb : ∀ j s a, |(b j s a : ℝ)| ≤ B)
    (j : Fin m) (d : K →₀ ℕ) (hd : d.degree ≤ j.val + 1) (a : J j) :
    |(sitePullbackFrequency site b j d a : ℝ)| ≤
      (Fintype.card S : ℝ) * Real.exp ((m : ℝ) * (P + 1)) * B := by
  have he (s : S) : |((d.prod (fun k n => site s k ^ n) : ℤ) : ℝ)| ≤
      Real.exp ((m : ℝ) * (P + 1)) := by
    have hh := (boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt)
      site hsite s ⟨d, hd⟩).abs_real_le
    have hh' : |((d.prod (fun k n => site s k ^ n) : ℤ) : ℝ)| ≤
        (exponentialSiteHeight m P : ℝ) := by
      simpa only [boundedSiteMatrix, Rat.cast_intCast] using hh
    exact hh'.trans (exponentialSiteHeight_le m hP)
  simp only [sitePullbackFrequency, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ s, |((d.prod (fun k n => site s k ^ n) : ℤ) : ℝ) * (b j s a : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : S, Real.exp ((m : ℝ) * (P + 1)) * B := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul]
      exact mul_le_mul (he s) (hb j s a) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by simp; ring

theorem sitePullbackFrequency_exp_bound {K S : Type*} [Fintype S] {m : ℕ}
    {J : Fin m → Type*} (site : S → K → ℤ) (b : ∀ j, Matrix S (J j) ℤ)
    {P : ℝ} (hP : 0 ≤ P) (hS : (Fintype.card S : ℝ) ≤ Real.exp P)
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (hb : ∀ j s a, |(b j s a : ℝ)| ≤ Real.exp P)
    (j : Fin m) (d : K →₀ ℕ) (hd : d.degree ≤ j.val + 1) (a : J j) :
    |(sitePullbackFrequency site b j d a : ℝ)| ≤ Real.exp (((m : ℝ) + 2) * (P + 1)) := by
  apply (sitePullbackFrequency_bound site b hP hsite hb j d hd a).trans
  calc
    _ ≤ Real.exp P * Real.exp ((m : ℝ) * (P + 1)) * Real.exp P := by gcongr
    _ = Real.exp (2 * P + (m : ℝ) * (P + 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
