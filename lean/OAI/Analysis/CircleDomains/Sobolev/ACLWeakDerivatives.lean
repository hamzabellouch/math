import OAI.Analysis.CircleDomains.Sobolev.RectangleDerivativeRepresentatives
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Integration by parts for the Borel representatives of ACL derivatives.
This converts the actual slice derivative into a planar weak derivative. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem integral_mul_horizontal_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hrep : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      G (x, y) = deriv (fun t => f (t, y)) x)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  have hcD : Continuous (fun p => (fderiv ℝ φ p) (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hcD.bounded_above_of_compact_support (hsupp.fderiv_apply (𝕜 := ℝ) (1, 0))
  obtain ⟨D, hD⟩ := hφ.continuous.bounded_above_of_compact_support hsupp
  have hl : Integrable (fun p => f p * (fderiv ℝ φ p) (1, 0))
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hf.mul_bdd hcD.aestronglyMeasurable (Eventually.of_forall hC)
  have hr : Integrable (fun p => G p * φ p)
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hG.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
  have hp (x y : ℝ) : deriv (fun t => φ (t, y)) x = (fderiv ℝ φ (x, y)) (1, 0) := by
    exact ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  have hzero (x y : ℝ) (hx : x ∉ Ioo a b) : φ (x, y) = 0 := by
    by_contra hn
    exact hx (hsub (subset_tsupport φ hn)).1
  have hline : ∀ᵐ y ∂volume.restrict (Icc c d),
      (∫x in Icc a b, f (x, y) * (fderiv ℝ φ (x, y)) (1, 0)) =
        -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
    filter_upwards [hac, hrep] with y hy hyr
    have hφline : AbsolutelyContinuousOnInterval (fun x => φ (x, y)) a b :=
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hi := hy.integral_mul_deriv_eq_deriv_mul hφline
    rw [hzero b y (by simp), hzero a y (by simp), mul_zero, mul_zero, sub_self,
      zero_sub] at hi
    simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hi
    calc
      _ = ∫x in Icc a b, f (x, y) * deriv (fun t => φ (t, y)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => congrArg (fun z => f (x, y) * z) (hp x y).symm
      _ = -(∫x in Icc a b, deriv (fun t => f (t, y)) x * φ (x, y)) := hi
      _ = -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
        congr 1
        exact integral_congr_ae (hyr.mono fun x hx => congrArg (fun z => z * φ (x, y)) hx.symm)
  have he : (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [he] at hl hr ⊢
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr, ← integral_neg]
  exact integral_congr_ae hline

theorem integral_mul_vertical_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hrep : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      G (x, y) = deriv (fun t => f (x, t)) y)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hswap : MeasurePreserving e
      (volume.restrict (Icc c d ×ˢ Icc a b))
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    change MeasurePreserving Prod.swap _ _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict]
    exact Measure.measurePreserving_swap
  have hs : tsupport (φ ∘ e) ⊆ Ioo c d ×ˢ Ioo a b := by
    change tsupport (φ ∘ e.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage φ e.toHomeomorph]
    intro p hp
    exact ⟨(hsub hp).2, (hsub hp).1⟩
  have hi := integral_mul_horizontal_deriv_eq_neg hcd
    (hswap.integrable_comp_of_integrable hf) (hswap.integrable_comp_of_integrable hG)
    hac hrep (hφ.comp e.contDiff) (hsupp.comp_homeomorph e.toHomeomorph) hs
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ (φ ∘ e) p) (1, 0) = (fderiv ℝ φ (e p)) (0, 1) := by
    rw [fderiv_comp p (hφ.differentiable (by simp)).differentiableAt e.differentiableAt,
      e.fderiv]
    rfl
  simp only [Function.comp_apply, hd] at hi
  calc
    _ = ∫p in Icc c d ×ˢ Icc a b, f (e p) * (fderiv ℝ φ (e p)) (0, 1) :=
      (hswap.integral_comp e.toHomeomorph.measurableEmbedding _).symm
    _ = -(∫p in Icc c d ×ˢ Icc a b, G (e p) * φ (e p)) := hi
    _ = _ := congrArg Neg.neg (hswap.integral_comp e.toHomeomorph.measurableEmbedding
      (fun p => G p * φ p))

end CircleDomainRigidity

end

end OAI
