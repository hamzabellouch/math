import OAI.Geometry.Zonotope.Support

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma abs_single_difference (i j k : ι) (hij : i ≠ j) :
    |((Pi.single i (1 : ℝ) : ι → ℝ)) k - ((Pi.single j (1 : ℝ) : ι → ℝ)) k| =
      ((Pi.single i (1 : ℝ) : ι → ℝ)) k + ((Pi.single j (1 : ℝ) : ι → ℝ)) k := by
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki, hkj]

lemma coordinate_difference_support (i j : ι) (hij : i ≠ j) :
    ((∑ k, |((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) +
      |∑ k, ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) / 2 = 1 := by
  have ha : (∑ k, |((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) = 2 := by
    calc
      _ = ∑ k, (((Pi.single i (1 : ℝ) : ι → ℝ)) k + ((Pi.single j (1 : ℝ) : ι → ℝ)) k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_single_difference i j k hij
      _ = 2 := by norm_num [Finset.sum_add_distrib, Pi.single_apply]
  have hs : (∑ k, ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k) = 0 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply]
  rw [ha, hs]
  norm_num

/-- Explicit coordinate tests suffice to recover the body from all support bounds. -/
theorem centered_eq_support_halfspaces :
    (centered : Set (ι → ℝ)) =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        ((∑ i, |u i|) + |∑ i, u i|) / 2} := by
  ext x
  constructor
  · intro hx u
    exact centered_support_le u x hx
  · intro hx
    apply (mem_centered_iff x).mpr
    constructor
    · intro i
      have hp := hx ((Pi.single i (1 : ℝ) : ι → ℝ))
      have hn := hx ((Pi.single i (-1 : ℝ) : ι → ℝ))
      have hp' : x i ≤ 1 := by simpa [Pi.single_apply, apply_ite] using hp
      have hn' : -x i ≤ 1 := by simpa [Pi.single_apply, apply_ite] using hn
      exact abs_le.mpr ⟨by linarith, hp'⟩
    · intro i j
      by_cases hij : i = j
      · subst j
        simp
      · have hp := hx ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ))
        have hn := hx ((Pi.single j (1 : ℝ) : ι → ℝ) - (Pi.single i (1 : ℝ) : ι → ℝ))
        rw [coordinate_difference_support i j hij] at hp
        rw [coordinate_difference_support j i (Ne.symm hij)] at hn
        have hp' : x i - x j ≤ 1 := by
          simpa [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply] using hp
        have hn' : x j - x i ≤ 1 := by
          simpa [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply] using hn
        exact abs_le.mpr ⟨by linarith, hp'⟩

end DiagonalZonotope

end

end OAI
