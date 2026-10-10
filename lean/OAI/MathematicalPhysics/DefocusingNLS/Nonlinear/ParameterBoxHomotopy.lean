import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailParameterContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleHomotopyCount

namespace OAI

/-! # The finite zero-tail count throughout the certified parameter box -/

open Set

namespace DefocusingNLS

attribute [local irreducible] spectralHomotopyDeterminant matchingHomotopyColumn backwardProduct

noncomputable def certifiedParameterSegment (center value t : ℝ) : ℝ :=
  center + t * (value - center)

@[simp] theorem certifiedParameterSegment_zero (c b : ℝ) :
    certifiedParameterSegment c b 0 = c := by simp [certifiedParameterSegment]

@[simp] theorem certifiedParameterSegment_one (c b : ℝ) :
    certifiedParameterSegment c b 1 = b := by simp [certifiedParameterSegment]

theorem certifiedParameterSegment_bound (C center value t : ℝ)
    (hc : 100000000 * center = C) (hb : |100000000 * value - C| ≤ 2)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |100000000 * certifiedParameterSegment center value t - C| ≤ 2 := by
  have he : 100000000 * certifiedParameterSegment center value t - C =
      t * (100000000 * value - C) := by
    calc
      100000000 * certifiedParameterSegment center value t - C =
          (1 - t) * (100000000 * center - C) + t * (100000000 * value - C) := by
        unfold certifiedParameterSegment
        ring
      _ = t * (100000000 * value - C) := by rw [sub_eq_zero.mpr hc]; ring
  rw [he, abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hb

theorem continuous_zeroTail_parameterSegment (ell : ℕ) (b Z : ℝ) :
    Continuous (fun x : ℝ × ℂ => spectralHomotopyDeterminant ell
      (certifiedParameterSegment (33477607 / 100000000) b x.1)
      (certifiedParameterSegment (270506819 / 100000000) Z x.1) 0 x.2) := by
  have hc : Continuous (fun x : ℝ × ℂ =>
      (certifiedParameterSegment (33477607 / 100000000) b x.1,
       certifiedParameterSegment (270506819 / 100000000) Z x.1, x.2)) := by
    unfold certifiedParameterSegment
    fun_prop
  simpa only [Function.comp_def] using (continuous_zeroTail_spectralDeterminant ell).comp hc

/-- The certified boundary stays zero-free along the straight parameter segment.
Only the published rectangle Rouché input is assumed. -/
theorem exists_zeroTail_parameter_count (hR : RectangleRouche) (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ W : ℝ, V < W → ∀ b Z : ℝ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      rectangleZeroCount W
          (spectralHomotopyDeterminant ell (33477607 / 100000000)
            (270506819 / 100000000) 0) =
        rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 0) := by
  obtain ⟨V, hV, he⟩ := exists_spectral_counting_boundary ell
  refine ⟨V, hV, ?_⟩
  intro W hW b Z hb hZ
  let B := certifiedParameterSegment (33477607 / 100000000) b
  let C := certifiedParameterSegment (270506819 / 100000000) Z
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |100000000 * B t - 33477607| ≤ 2 :=
    certifiedParameterSegment_bound _ _ b t (by norm_num) hb ht
  have hC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |100000000 * C t - 270506819| ≤ 2 :=
    certifiedParameterSegment_bound _ _ Z t (by norm_num) hZ ht
  have hC0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : C t ≠ 0 := by
    have hh := hC t ht
    intro hz
    norm_num [hz] at hh
  have hc := rectangleZeroCount_homotopy hR W (hV.trans hW)
    (fun t => spectralHomotopyDeterminant ell (B t) (C t) 0) ?_ ?_ ?_
  · simpa only [B, C, certifiedParameterSegment_zero, certifiedParameterSegment_one] using hc
  · intro t ht z hz
    exact analyticAt_spectralHomotopyDeterminant ell (B t) (C t) 0 z (hC0 t ht) hz.1
  · intro t ht z hz
    exact (continuous_zeroTail_parameterSegment ell b Z).continuousAt
  · intro t ht z hz
    apply he (B t) (C t) 0 z (hB t ht) (hC t ht) (by norm_num) (by norm_num)
    rcases (mem_countingRectangleBoundary_iff W z).mp hz with ⟨hrect, hedge⟩
    rcases hedge with hleft | hright | hbottom | htop
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright.ge)
    · exact Or.inr (Or.inr ⟨hrect.1, by
        rw [hbottom, abs_neg, abs_of_pos (hV.trans hW)]
        exact hW⟩)
    · exact Or.inr (Or.inr ⟨hrect.1, by
        rw [htop, abs_of_pos (hV.trans hW)]
        exact hW⟩)

end DefocusingNLS

end OAI
