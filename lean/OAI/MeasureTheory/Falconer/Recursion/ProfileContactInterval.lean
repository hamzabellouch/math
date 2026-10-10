import OAI.MeasureTheory.Falconer.Recursion.ProfileRightContact
import OAI.MeasureTheory.Falconer.Fourier.ProfileDerivativePoint

namespace OAI

/-! # The three contact intervals used by radial improvement

This proves Lemma `prep:contact` of the supplied manuscript. The proof only
needs the Lipschitz and lower-profile hypotheses; monotonicity is not needed.
-/

namespace Falconer
open Set
open scoped NNReal

theorem profile_sub_linear_lipschitz {m : ℝ → ℝ} {K : ℝ≥0}
    (hm : LipschitzOnWith K m (Icc 0 1)) (q : ℝ) :
    LipschitzOnWith (Real.toNNReal ((K:ℝ)+|q|)) (fun u => m u-q*u) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  rw [Real.dist_eq,Real.dist_eq]
  calc
    |(m x-q*x)-(m y-q*y)| = |(m x-m y)-q*(x-y)| := by congr 1; ring
    _ ≤ |m x-m y|+|q*(x-y)| := abs_sub _ _
    _ ≤ (K:ℝ)*|x-y|+|q| *|x-y| := by
      rw [abs_mul]
      exact add_le_add (by simpa only [Real.dist_eq] using hm.dist_le_mul x hx y hy) le_rfl
    _ = ((K:ℝ)+|q|)*|x-y| := by ring

theorem profile_contact_interval {m : ℝ → ℝ} {K : ℝ≥0} {q t s : ℝ}
    (hm : LipschitzOnWith K m (Icc 0 1)) (hzero : m 0 = 0)
    (hlower : ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u) (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧
      (∀ w ∈ Icc 0 A, q*w ≤ m w) ∧
      (∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A) ∧
      (∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B) := by
  let g := fun u => m u-q*u
  let F := profileSuffixMinimum g
  have hg := profile_sub_linear_lipschitz hm q
  have hgc := hg.continuousOn
  have hFL := profileSuffixMinimum_lipschitz hg
  have hF0 : F 0 = 0 := by
    apply le_antisymm
    · simpa [F,g,hzero] using profileSuffixMinimum_le hgc
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    · obtain ⟨z,hz,he,_⟩ := profileSuffixMinimum_attained hgc
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      change 0 ≤ profileSuffixMinimum g 0
      rw [he]
      have hh := hlower z hz
      have hp := mul_nonneg (sub_nonneg.mpr (hqt.trans hts).le) hz.1
      change 0 ≤ m z-q*z
      nlinarith
  have hF1 : F 1 = m 1-q := by
    obtain ⟨z,hz,he,_⟩ := profileSuffixMinimum_attained hgc
      (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    have hz1 : z = 1 := le_antisymm hz.2 hz.1
    simpa [F,g,hz1] using he
  have hinc : t-q < F 1-F 0 := by
    rw [hF0,hF1]
    have hh := hlower 1 (by constructor <;> norm_num)
    linarith
  obtain ⟨A,hA,l,hd,hl⟩ := lipschitz_unit_interval_derivative_point hFL hinc
  have hl0 : 0 < l := (sub_pos.mpr hqt).trans hl
  have hcontactA : F A = g A := profileSuffixMinimum_contact_of_pos_deriv hgc hA hd hl0
  obtain ⟨η,hη,hsec⟩ := hasDerivAt_right_secant_lower hd hl
  let T := min (2*A) (min 1 (A+η))
  have hAT : A < T := by
    dsimp [T]
    exact lt_min (by linarith [hA.1]) (lt_min hA.2 (by linarith))
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨B,hAB,hBT,hcontactB⟩ := profileSuffixMinimum_right_contact hg hA hd hl0 hAT hT1
  have hB1 : B < 1 := hBT.trans_le hT1
  have hB2 : B < 2*A := hBT.trans_le (min_le_left _ _)
  have hBη : B < A+η := hBT.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A,B,hA.1,hAB,hB1,hB2,?_,?_,?_⟩
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1,hw.2.trans hA.2.le⟩
    have hp := mul_nonneg (sub_nonneg.mpr (hqt.trans hts).le) hw.1
    nlinarith [hlower w hwI]
  · intro w hw
    by_cases he : w = A
    · subst w
      simp
    have hAw : A < w := lt_of_le_of_ne hw.1 (Ne.symm he)
    have hh := hsec w hAw (hw.2.trans_lt hBη)
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hw.1,hw.2.trans hB1.le⟩
    have hFw := profileSuffixMinimum_le hgc hwI ⟨le_rfl,hwI.2⟩
    change F w ≤ g w at hFw
    change (t-q)*(w-A) < F w-F A at hh
    rw [hcontactA] at hh
    dsimp [g] at hh hFw
    linarith
  · intro w hw
    have hBI : B ∈ Icc (0:ℝ) 1 := ⟨(hA.1.trans hAB).le,hB1.le⟩
    have hh := profileSuffixMinimum_le hgc hBI hw
    rw [hcontactB] at hh
    linarith

end Falconer

end OAI
