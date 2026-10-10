import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

namespace Problem336AdditiveD139

theorem bivariate_stable_root_im_nonpos (a b c d : ℂ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      a + b * z + c * w + d * z * w ≠ 0)
    (w : ℂ) (hw : 0 < w.im) :
    (-(a + c * w) / (b + d * w)).im ≤ 0 := by
  by_cases hden : b + d * w = 0
  · simp [hden]
  · by_contra h
    have hz : 0 < (-(a + c * w) / (b + d * w)).im := lt_of_not_ge h
    apply hstable (-(a + c * w) / (b + d * w)) w hz hw
    calc
      _ = a + c * w + (-(a + c * w) / (b + d * w)) * (b + d * w) := by ring
      _ = 0 := by rw [div_mul_cancel₀ _ hden]; ring

theorem bivariate_stable_rayleigh (a b c d : ℝ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      (a : ℂ) + b * z + c * w + d * z * w ≠ 0) :
    a * d ≤ b * c := by
  by_contra hle
  have hdiff : 0 < a * d - b * c := by linarith
  have hden : 0 < b ^ 2 + d ^ 2 := by
    by_contra hn
    have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    simp [hb, hd] at hdiff
  let z : ℂ := ⟨-(a * b + c * d) / (b ^ 2 + d ^ 2),
    (a * d - b * c) / (b ^ 2 + d ^ 2)⟩
  have hz : 0 < z.im := div_pos hdiff hden
  have hzero : (a : ℂ) + b * z + c * Complex.I + d * z * Complex.I = 0 := by
    apply Complex.ext
    · simp [z, Complex.mul_re, Complex.mul_im]
      field_simp
      all_goals ring
    · simp [z, Complex.mul_re, Complex.mul_im]
      field_simp
      all_goals ring
  exact hstable z Complex.I hz (by simp) hzero

theorem bivariate_stable_limit_rayleigh_of_eventually {ι : Type u_1} {l : Filter ι} [l.NeBot]
    (A B C D : ι → ℂ) (a b c d : ℝ)
    (hA : Filter.Tendsto A l (nhds (a : ℂ)))
    (hB : Filter.Tendsto B l (nhds (b : ℂ)))
    (hC : Filter.Tendsto C l (nhds (c : ℂ)))
    (hD : Filter.Tendsto D l (nhds (d : ℂ)))
    (hstable : ∀ᶠ n in l, ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A n + B n * z + C n * w + D n * z * w ≠ 0) :
    a * d ≤ b * c := by
  by_contra hle
  have hdiff : 0 < a * d - b * c := by linarith
  have hden : (b : ℂ) + d * Complex.I ≠ 0 := by
    intro hz
    have hb : b = 0 := by simpa using congrArg Complex.re hz
    have hd : d = 0 := by simpa using congrArg Complex.im hz
    simp [hb, hd] at hdiff
  have hlim := ((hA.add (hC.mul_const Complex.I)).neg).div
    (hB.add (hD.mul_const Complex.I)) hden
  have him : ( -((a : ℂ) + c * Complex.I) / ((b : ℂ) + d * Complex.I)).im ≤ 0 :=
    le_of_tendsto (Complex.continuous_im.tendsto _ |>.comp hlim)
      (hstable.mono fun n hn =>
        bivariate_stable_root_im_nonpos (A n) (B n) (C n) (D n)
          hn Complex.I (by simp))
  have hn : 0 < Complex.normSq ((b : ℂ) + d * Complex.I) :=
    Complex.normSq_pos.mpr hden
  have hformula : (-((a : ℂ) + c * Complex.I) / ((b : ℂ) + d * Complex.I)).im =
      (a * d - b * c) / Complex.normSq ((b : ℂ) + d * Complex.I) := by
    simp [Complex.div_im]
    ring
  rw [hformula] at him
  exact (not_lt_of_ge him) (div_pos hdiff hn)

theorem bivariate_stable_limit_rayleigh {ι : Type u_2} {l : Filter ι} [l.NeBot]
    (A B C D : ι → ℂ) (a b c d : ℝ)
    (hA : Filter.Tendsto A l (nhds (a : ℂ)))
    (hB : Filter.Tendsto B l (nhds (b : ℂ)))
    (hC : Filter.Tendsto C l (nhds (c : ℂ)))
    (hD : Filter.Tendsto D l (nhds (d : ℂ)))
    (hstable : ∀ n, ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A n + B n * z + C n * w + D n * z * w ≠ 0) :
    a * d ≤ b * c :=
  bivariate_stable_limit_rayleigh_of_eventually A B C D a b c d hA hB hC hD
    (Filter.Eventually.of_forall hstable)

theorem bivariate_continuous_limit_rayleigh
    (A B C D : ℝ → ℂ) (a b c d : ℝ)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0)
    (hA0 : A 0 = (a : ℂ)) (hB0 : B 0 = (b : ℂ))
    (hC0 : C 0 = (c : ℂ)) (hD0 : D 0 = (d : ℂ))
    (hstable : ∀ t : ℝ, 0 < t → ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A t + B t * z + C t * w + D t * z * w ≠ 0) :
    a * d ≤ b * c := by
  apply bivariate_stable_limit_rayleigh_of_eventually
    (l := nhdsWithin 0 (Set.Ioi 0)) A B C D a b c d
  · simpa [hA0] using hA.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hB0] using hB.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hC0] using hC.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [hD0] using hD.tendsto.mono_left nhdsWithin_le_nhds
  · have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    exact hpos.mono fun t ht => hstable t ht

end Problem336AdditiveD139

end

end OAI
