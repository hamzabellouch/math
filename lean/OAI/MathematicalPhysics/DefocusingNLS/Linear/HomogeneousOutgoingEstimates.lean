import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingMatrix
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingLogJets

namespace OAI

/-! # Bounded physical derivative rows from the normalized outgoing columns

The radial powers in the value matrix and its inverse cancel. The
remaining bound depends only on the bounded normalized jets and inverse.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ

noncomputable def homogeneousPhysicalLogColumn (νp νm : ℂ)
    (f g : ℝ → ℂ) (t : ℝ) : V :=
  (Complex.exp (νp * (t : ℂ)) * f t, Complex.exp (νm * (t : ℂ)) * g t)

noncomputable def homogeneousNormalizedEulerColumn (νp νm : ℂ)
    (f g : ℝ → ℂ) (n : ℕ) (t : ℝ) : V :=
  (homogeneousNormalizedEuler νp f n t, homogeneousNormalizedEuler νm g n t)

theorem homogeneousNormalizedEulerColumn_bound (νp νm : ℂ)
    (f g : ℝ → ℂ) (hf : HasLogJetBound 0 f) (hg : HasLogJetBound 0 g) (n : ℕ) :
    HasLogJetBound 0 (homogeneousNormalizedEulerColumn νp νm f g n) :=
  (homogeneousNormalizedEuler_bound νp f hf n).pair
    (homogeneousNormalizedEuler_bound νm g hg n)

theorem homogeneousPhysicalLogColumn_diagonal (νp νm : ℂ)
    (f g : ℝ → ℂ) (t : ℝ) :
    homogeneousPhysicalLogColumn νp νm f g t =
      homogeneousDiagonal (Complex.exp (νp * (t : ℂ))) (Complex.exp (νm * (t : ℂ)))
        (f t, g t) := by
  rw [homogeneousDiagonal_apply]
  rfl

theorem homogeneousPhysicalLogColumn_euler (νp νm : ℂ)
    (f g : ℝ → ℂ) (L : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioi L))
    (hg : ContDiffOn ℝ ∞ g (Ioi L)) (n : ℕ) (t : ℝ) (ht : L < t) :
    homogeneousEulerDeriv (homogeneousPhysicalLogColumn νp νm f g) n t =
      homogeneousDiagonal (Complex.exp (νp * (t : ℂ))) (Complex.exp (νm * (t : ℂ)))
        (homogeneousNormalizedEulerColumn νp νm f g n t) := by
  rw [homogeneousDiagonal_apply]
  exact homogeneousEulerDeriv_normalized νp νm f g L hf hg n t ht

theorem homogeneousOutgoingDerivativeRows_bound (νp νm : ℂ) (hν : νp.re = νm.re)
    (fp gp fm gm : ℝ → ℂ)
    (hfp : HasLogJetBound 0 fp) (hgp : HasLogJetBound 0 gp)
    (hfm : HasLogJetBound 0 fm) (hgm : HasLogJetBound 0 gm)
    (hp : Tendsto (fun t => (fp t, gp t)) atTop (𝓝 (1, 0)))
    (hm : Tendsto (fun t => (fm t, gm t)) atTop (𝓝 (0, 1))) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in atTop,
      spectralValueDet (homogeneousPhysicalLogColumn νp νm fp gp t)
        (homogeneousPhysicalLogColumn νp νm fm gm t) ≠ 0 ∧
      ‖spectralTwoColumns
          (homogeneousEulerDeriv (homogeneousPhysicalLogColumn νp νm fp gp) n t)
          (homogeneousEulerDeriv (homogeneousPhysicalLogColumn νp νm fm gm) n t) *
        spectralValueInverse (homogeneousPhysicalLogColumn νp νm fp gp t)
          (homogeneousPhysicalLogColumn νp νm fm gm t)‖ ≤ K := by
  obtain ⟨Lf, hLf⟩ := hfp.smooth
  obtain ⟨Lg, hLg⟩ := hgp.smooth
  obtain ⟨Lh, hLh⟩ := hfm.smooth
  obtain ⟨Li, hLi⟩ := hgm.smooth
  let L := max (max Lf Lg) (max Lh Li)
  have hLf' : ContDiffOn ℝ ∞ fp (Ioi L) :=
    hLf.mono (Ioi_subset_Ioi ((le_max_left Lf Lg).trans (le_max_left _ _)))
  have hLg' : ContDiffOn ℝ ∞ gp (Ioi L) :=
    hLg.mono (Ioi_subset_Ioi ((le_max_right Lf Lg).trans (le_max_left _ _)))
  have hLh' : ContDiffOn ℝ ∞ fm (Ioi L) :=
    hLh.mono (Ioi_subset_Ioi ((le_max_left Lh Li).trans (le_max_right _ _)))
  have hLi' : ContDiffOn ℝ ∞ gm (Ioi L) :=
    hLi.mono (Ioi_subset_Ioi ((le_max_right Lh Li).trans (le_max_right _ _)))
  obtain ⟨J, hJ, hInv⟩ := homogeneousNormalizedInverse_bound _ _ hp hm
  obtain ⟨A, hA, ha⟩ := (homogeneousNormalizedEulerColumn_bound νp νm fp gp hfp hgp n).bound 0
  obtain ⟨B, hB, hb⟩ := (homogeneousNormalizedEulerColumn_bound νp νm fm gm hfm hgm n).bound 0
  refine ⟨(A + B) * J, mul_nonneg (add_nonneg hA hB) hJ, ?_⟩
  filter_upwards [hInv, ha, hb, eventually_gt_atTop L] with t hi htA htB htL
  simp only [iteratedDeriv_zero, zero_mul, Real.exp_zero, mul_one] at htA htB
  have hnormp : ‖Complex.exp (νp * (t : ℂ))‖ = Real.exp (νp.re * t) := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hnormm : ‖Complex.exp (νm * (t : ℂ))‖ = Real.exp (νp.re * t) := by
    simpa only [hν] using (show ‖Complex.exp (νm * (t : ℂ))‖ = Real.exp (νm.re * t) by
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero])
  refine ⟨?_, ?_⟩
  · simp only [homogeneousPhysicalLogColumn_diagonal, homogeneousDiagonal_det]
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)) hi.1
  · rw [homogeneousPhysicalLogColumn_euler νp νm fp gp L hLf' hLg' n t htL,
      homogeneousPhysicalLogColumn_euler νp νm fm gm L hLh' hLi' n t htL]
    simp only [homogeneousPhysicalLogColumn_diagonal]
    apply (homogeneousDiagonal_remainder_norm _ _ (Real.exp (νp.re * t))
      (Real.exp_pos _) hnormp hnormm (fp t, gp t) (fm t, gm t) _ _ hi.1).trans
    apply (mul_le_mul_of_nonneg_right (homogeneousTwoColumns_norm _ _) (norm_nonneg _)).trans
    exact mul_le_mul (add_le_add htA htB) hi.2 (norm_nonneg _)
      (add_nonneg hA hB)

end DefocusingNLS

end OAI
