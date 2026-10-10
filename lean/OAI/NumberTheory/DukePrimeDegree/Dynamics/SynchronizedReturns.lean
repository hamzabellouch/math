import OAI.NumberTheory.DukePrimeDegree.Geometry.SynchronizedAnnuli
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoAnnularEqualReturns
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafRegularSet

namespace OAI

/-!
# Synchronized compact shearing pairs with equal leaves

The four recurrence windows produce the small central portions of both
leaf annuli at one common diagonal time. On the regular set, the
measurable kernel is the intrinsic leaf. The annular selection then
avoids the leafwise exceptional sets for rebasing, so both compact
return pairs have equal intrinsic leaves.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_synchronized_annular_equal_leaf_returns
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (g : G (d + 1))
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (hT : 1 ≤ rootShearingLogTime i j g)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g)
    (K G H : Set (X (d + 1))) (z : Fin 2 → X (d + 1))
    (ρ ε : ℝ) (c a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hsecond : 16 / ρ ≤ ρ * C) (hcoeff : c + c + a < 1)
    (hregular : ∀ x ∈ G,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z k) (Metric.ball 0 r))
    (heq : intrinsicRootKernel hij μ hfree (z 0) = intrinsicRootKernel hij μ hfree (z 1))
    (hcov : ∀ k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z k) t)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 (rootShearingLogTime i j g), ∃ t : Fin 2 → ℝ,
      let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
      let κ := rootShearingKappa i j (rootPairConjugate i j τ g)
      (∀ b, rightAction (x 0) (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        rightAction (x 1) (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        intrinsicRootLeaf hij μ (rightAction (x 0)
          (Matrix.SpecialLinearGroup.transvection hij (t b))) =
        intrinsicRootLeaf hij μ (rightAction (x 1)
          (Matrix.SpecialLinearGroup.transvection hij (t b)))) ∧
      0 < κ ∧ ρ ≤ |κ * t 0| ∧ |κ * t 0| ≤ 1 ∧
      16 / ρ ≤ |κ * t 1| ∧ |κ * t 1| ≤ C := by
  obtain ⟨τ, hτ, hxG, heqτ, hr, hmass⟩ := exists_synchronized_leaf_annuli
    d hij μ hfree g hnot hsmall hT C hC hlog G H z ρ ε a hε hHsmall hpos heq hcov hcontrol
  let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
  let κ := rootShearingKappa i j (rootPairConjugate i j τ g)
  have hκ : 0 < κ := by
    have h := hr 0
    change 0 < (if (0 : Fin 2) = 0 then 1 else C) * κ⁻¹ at h
    simpa only [ite_true, one_mul, inv_pos] using h
  have hxreg := hregular (x 0) (hxG 0)
  have hyreg := hregular (x 1) (hxG 1)
  have hleaf : intrinsicRootLeaf hij μ (x 0) = intrinsicRootLeaf hij μ (x 1) :=
    hxreg.1.symm.trans (heqτ.trans hyreg.1)
  have hmass' (b : Fin 2) : intrinsicRootLeaf hij μ (x 0)
      (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) / κ))) <
        a * intrinsicRootLeaf hij μ (x 0)
          (Metric.closedBall 0 ((if b = 0 then 1 else C) / κ)) := by
    have hm := hmass 0 b
    change intrinsicRootKernel hij μ hfree (x 0)
      (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) * κ⁻¹))) <
        a * intrinsicRootKernel hij μ hfree (x 0)
          (Metric.closedBall 0 ((if b = 0 then 1 else C) * κ⁻¹)) at hm
    rw [hxreg.1] at hm
    simpa only [div_eq_mul_inv] using hm
  obtain ⟨t, hret, hlo, hfirst, hsecond', hupp⟩ :=
    exists_two_normalized_annular_equal_leaf_returns hij μ K G c a hgood
      (x 0) (x 1) (hxG 0) (hxG 1) hleaf hxreg.2.2 hyreg.2.2 hxreg.2.1
      κ ρ C hκ hC hsecond hmass' hcoeff
  exact ⟨τ, hτ, t, hret, hκ, hlo, hfirst, hsecond', hupp⟩

end DukePrimeDegree

end

end OAI
