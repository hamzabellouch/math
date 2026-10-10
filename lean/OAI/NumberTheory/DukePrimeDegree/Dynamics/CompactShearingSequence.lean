import OAI.NumberTheory.DukePrimeDegree.Dynamics.SynchronizedReturns
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingReturnGeometry
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSelectedConvergence

namespace OAI

/-!
# Compact equal-leaf shearing sequences

The synchronized annular return theorem applies to every member of an
initial noncentral sequence. The selected diagonal conjugates still
tend to identity, and the two compact return pairs have equal leaves
and the signed conjugation convention required by shearing compactness.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_equal_leaf_shearing_sequence
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (g : ℕ → G (d + 1)) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (hT : ∀ m, 1 ≤ rootShearingLogTime i j (g m))
    (C : ℝ) (hC : 1 ≤ C) (hlog : ∀ m, Real.log C ≤ rootShearingLogTime i j (g m))
    (K G H : Set (X (d + 1))) (z : ℕ → Fin 2 → X (d + 1))
    (hpair : ∀ m, rightAction (z m 0) (g m) = z m 1)
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
    (hpos : ∀ m k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z m k) (Metric.ball 0 r))
    (heq : ∀ m, intrinsicRootKernel hij μ hfree (z m 0) =
      intrinsicRootKernel hij μ hfree (z m 1))
    (hcov : ∀ m k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z m k) t)
    (hcontrol : ∀ m k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ (γ : ℕ → PrimeDegreePackets.G (d + 1))
      (p : ℕ → Fin 2 → X (d + 1)) (t : ℕ → Fin 2 → ℝ),
      Tendsto γ atTop (𝓝 1) ∧ ∀ m,
        0 < rootShearingKappa i j (γ m) ∧ rootShearingKappa i j (γ m) ≤ 1 ∧
        (∀ b, p m b ∈ K ∧
          rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
            Matrix.SpecialLinearGroup.transvection hij (-t m b)) ∈ K ∧
          intrinsicRootLeaf hij μ (p m b) = intrinsicRootLeaf hij μ
            (rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
              Matrix.SpecialLinearGroup.transvection hij (-t m b)))) ∧
        ρ ≤ |rootShearingKappa i j (γ m) * t m 0| ∧
        |rootShearingKappa i j (γ m) * t m 0| ≤ 1 ∧
        16 / ρ ≤ |rootShearingKappa i j (γ m) * t m 1| ∧
        |rootShearingKappa i j (γ m) * t m 1| ≤ C := by
  have hex (m : ℕ) := exists_synchronized_annular_equal_leaf_returns d hij μ hfree
    (g m) (hnot m) (hsmall m) (hT m) C hC (hlog m) K G H (z m) ρ ε c a hε hsecond
    hcoeff hregular hgood hHsmall (hpos m) (heq m) (hcov m) (hcontrol m)
  choose τ hτ r hr using hex
  let γ := fun m => rootPairConjugate i j (τ m) (g m)
  let x := fun m k => rightAction (z m k) (rootPairFlow i j (-τ m))
  let p := fun m b => rightAction (x m 0) (Matrix.SpecialLinearGroup.transvection hij (r m b))
  have hxpair (m : ℕ) : rightAction (x m 0) (γ m) = x m 1 := by
    change rightAction (rightAction (z m 0) (rootPairFlow i j (-τ m)))
      (rootPairConjugate i j (τ m) (g m)) = _
    rw [rootPairConjugate_rightAction, hpair]
  have hp (m : ℕ) (b : Fin 2) : rightAction (p m b)
      (Matrix.SpecialLinearGroup.transvection hij (-(r m b)) * γ m *
        Matrix.SpecialLinearGroup.transvection hij (r m b)) =
      rightAction (x m 1) (Matrix.SpecialLinearGroup.transvection hij (r m b)) := by
    exact (rootConjugate_rightAction hij (x m 0) (γ m) (r m b)).trans
      (congrArg (fun y => rightAction y (Matrix.SpecialLinearGroup.transvection hij (r m b)))
        (hxpair m))
  refine ⟨γ, p, fun m b => -(r m b),
    rootPairConjugate_selected_tendsto_one hij g hg hnot hsmall τ
      (fun m => ⟨(hτ m).1.le, (hτ m).2⟩), ?_⟩
  intro m
  have hκ : rootShearingKappa i j (γ m) ≤ 1 :=
    (rootShearingKappa_window_bound hij (g m) (hnot m) (hsmall m) (τ m)
      ⟨(hτ m).1.le, (hτ m).2⟩).trans
        (Real.exp_le_one_iff.mpr (by linarith [hT m]))
  refine ⟨(hr m).2.1, hκ, ?_, ?_⟩
  · intro b
    simp only [neg_neg, hp]
    exact (hr m).1 b
  · simpa only [mul_neg, abs_neg] using (hr m).2.2

end DukePrimeDegree

end

end OAI
