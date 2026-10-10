import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.JensenGaps
import OAI.InformationTheory.BooleanNoise.CubeVariance
import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.KRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace OAI

open Set

namespace LeanBlast.CourtadeKumar

theorem function_increment_le_of_lipschitz_deriv
    (F : ℝ → ℝ) (C : ℝ)
    (hcont : ContinuousOn F (Ici 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ F x)
    (hlip : ∀ x y : ℝ, 0 < x → 0 < y →
      |deriv F x - deriv F y| ≤ C * |x - y|)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    {Je Jm Sa : ℝ} (hJm : 0 ≤ Jm) (hJe : Jm ≤ Je) (hSa : 0 ≤ Sa) :
    F (Je + Sa) - F (Je + Sa - Jm) ≤ F Je + C * Jm * Sa := by
  let G : ℝ → ℝ := fun t => F (Je + t) - F (Je - Jm + t)
  have hJe0 : 0 ≤ Je := hJm.trans hJe
  have hbase : 0 ≤ Je - Jm := sub_nonneg.mpr hJe
  have hGcont : ContinuousOn G (Ici 0) := by
    apply ContinuousOn.sub
    · exact hcont.comp (continuous_const.add continuous_id).continuousOn
        (fun t ht => add_nonneg hJe0 ht)
    · exact hcont.comp (continuous_const.add continuous_id).continuousOn
        (fun t ht => add_nonneg hbase ht)
  have hGderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt G (deriv F (Je + t) - deriv F (Je - Jm + t)) t := by
    intro t ht
    exact ((hdiff (Je + t) (add_pos_of_nonneg_of_pos hJe0 ht)).hasDerivAt.comp_const_add Je t).sub
      ((hdiff (Je - Jm + t) (add_pos_of_nonneg_of_pos hbase ht)).hasDerivAt.comp_const_add
        (Je - Jm) t)
  have hGdiff : DifferentiableOn ℝ G (interior (Ici 0)) := by
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hGderiv t ht0).differentiableAt.differentiableWithinAt
  have hGbound : ∀ t ∈ interior (Ici 0), deriv G t ≤ C * Jm := by
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(hGderiv t ht0).deriv]
    calc
      _ ≤ |deriv F (Je + t) - deriv F (Je - Jm + t)| := le_abs_self _
      _ ≤ C * |(Je + t) - (Je - Jm + t)| :=
        hlip _ _ (add_pos_of_nonneg_of_pos hJe0 ht0) (add_pos_of_nonneg_of_pos hbase ht0)
      _ = C * Jm := by rw [show (Je + t) - (Je - Jm + t) = Jm by ring, abs_of_nonneg hJm]
  have hstep := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hGcont hGdiff hGbound 0 (by simp) Sa hSa hSa
  simp only [G, add_zero, sub_zero] at hstep
  rw [show Je - Jm + Sa = Je + Sa - Jm by ring] at hstep
  linarith [hnonneg (Je - Jm) hbase]

theorem general_dissipation_step_algebra (F : ℝ → ℝ)
    {S Je Jm Sa V Drestr Dpair : ℝ}
    (hrestr : 2 * (S - Jm) + F (S - Jm) ≤ Drestr)
    (hpair : F Je + V ≤ Dpair - 2 * Jm)
    (hvariance : Jm * Sa / ell ≤ V)
    (hincrement : F S - F (S - Jm) ≤ F Je + Jm * Sa / ell) :
    2 * S + F S ≤ Drestr + Dpair := by
  linarith

theorem restriction_bound_of_convex (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ici 0) F) {S₁ S₀ D₁ D₀ : ℝ}
    (hS₁ : 0 ≤ S₁) (hS₀ : 0 ≤ S₀)
    (hD₁ : 2 * S₁ + F S₁ ≤ D₁) (hD₀ : 2 * S₀ + F S₀ ≤ D₀) :
    2 * ((S₁ + S₀) / 2) + F ((S₁ + S₀) / 2) ≤ (D₁ + D₀) / 2 := by
  have hmid := hF.2 hS₁ hS₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1 / 2 : ℝ) * S₁ + (1 / 2 : ℝ) * S₀ = (S₁ + S₀) / 2 by ring] at hmid
  linarith

theorem averaged_remainder_bound {n : ℕ} (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ici 0) F) (J d : Cube n → ℝ)
    (hJ : ∀ x, 0 ≤ J x) (hpoint : ∀ x, F (J x) ≤ d x - 2 * J x)
    {Jm V : ℝ} (hgap : V ≤ 2 * (cubeAverage J - Jm)) :
    F (cubeAverage J) + V ≤ cubeAverage d - 2 * Jm := by
  have havg : cubeAverage (fun x => F (J x)) ≤ cubeAverage (fun x => d x - 2 * J x) := by
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by positivity)
  have hidentity : cubeAverage (fun x => d x - 2 * J x) =
      cubeAverage d - 2 * cubeAverage J := by
    simp [cubeAverage, Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div, mul_div_assoc]
  rw [hidentity] at havg
  have hjensen := convexOn_cubeAverage_le F hF J hJ
  linarith

theorem general_dissipation_of_K_estimates
    (hconvex : ConvexOn ℝ (Ici 0) K)
    (hincrement : ∀ {Je Jm Sa : ℝ}, 0 ≤ Jm → Jm ≤ Je → 0 ≤ Sa →
      K (Je + Sa) - K (Je + Sa - Jm) ≤ K Je + Jm * Sa / ell)
    (hpoint : ∀ (a b : ℝ), |a| + |b| < 1 →
      K (pairEntropyGap a b) ≤ pairDissipation a b - 2 * pairEntropyGap a b) :
    ∀ {n : ℕ} (g : Cube n → ℝ), IsInterior g →
      2 * informationDeficit g + K (informationDeficit g) ≤ dissipation g := by
  intro n
  induction n with
  | zero =>
      intro g _
      simp
  | succ n ih =>
      intro g hg
      let a := pairMean g
      let b := pairHalfDifference g
      let J := fun x => pairEntropyGap (a x) (b x)
      let Je := cubeAverage J
      let Jm := pairEntropyGap (cubeAverage a) (cubeAverage b)
      let Sa := informationDeficit a
      let V := cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)
      have hdom : ∀ x, |a x| + |b x| < 1 := hg.pairDomain
      have hSa : 0 ≤ Sa := informationDeficit_nonneg hg.pairMean
      have hJm : 0 ≤ Jm := pairEntropyGap_nonneg _ _ (cubeAverage_pairDomain hdom)
      have hJmJe : Jm ≤ Je := pair_jensen_gap_nonneg a b hdom
      have hrestr := restriction_bound_of_convex K hconvex
        (informationDeficit_nonneg (hg.restrict true))
        (informationDeficit_nonneg (hg.restrict false))
        (ih (restrict g true) (hg.restrict true))
        (ih (restrict g false) (hg.restrict false))
      rw [informationDeficit_split] at hrestr
      have hpairavg : K Je + V ≤
          cubeAverage (fun x => pairDissipation (a x) (b x)) - 2 * Jm :=
        averaged_remainder_bound K hconvex J (fun x => pairDissipation (a x) (b x))
          (fun x => pairEntropyGap_nonneg _ _ (hdom x))
          (fun x => hpoint _ _ (hdom x)) (pair_jensen_gap a b hdom)
      have hvariance : Jm * Sa / ell ≤ V := entropy_product_le_variance_gap a b hdom
      have hinc := hincrement hJm hJmJe hSa
      have hS : informationDeficit g = Je + Sa := by
        dsimp only [Je, J, Sa, a, b]
        rw [informationDeficit_eq_pairMean_add]
        ring
      rw [← hS] at hinc
      have htotal := general_dissipation_step_algebra K hrestr hpairavg hvariance hinc
      rw [dissipation_split]
      exact htotal

theorem K_increment {Je Jm Sa : ℝ}
    (hJm : 0 ≤ Jm) (hJe : Jm ≤ Je) (hSa : 0 ≤ Sa) :
    K (Je + Sa) - K (Je + Sa - Jm) ≤ K Je + Jm * Sa / ell := by
  have h := function_increment_le_of_lipschitz_deriv K (1 / ell) continuousOn_K
    (fun x hx => (hasDerivAt_K hx.le).differentiableAt)
    (fun x y hx hy => by
      rw [(hasDerivAt_K hx.le).deriv, (hasDerivAt_K hy.le).deriv]
      exact KDeriv_lipschitz x y)
    (fun x _ => K_nonneg x) hJm hJe hSa
  calc
    _ ≤ K Je + (1 / ell) * Jm * Sa := h
    _ = K Je + Jm * Sa / ell := by ring

theorem general_dissipation {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g + K (informationDeficit g) ≤ dissipation g := by
  apply general_dissipation_of_K_estimates convexOn_K K_increment ?_ g hg
  intro a b hdom
  exact (K_le_rGap (pairEntropyGap_nonneg a b hdom) (pairEntropyGap_lt_ell a b hdom)).trans
    (rGap_pairEntropyGap_le a b hdom)

theorem small_information_dissipation {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g)
    (hS : informationDeficit g ≤ s0) : r (informationDeficit g) ≤ dissipation g := by
  have h := general_dissipation g hg
  rw [K_eq_rGap_nonneg (informationDeficit_nonneg hg) hS, rGap] at h
  linarith

end LeanBlast.CourtadeKumar

end OAI
