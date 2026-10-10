import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafScaleComposition
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCandidateWindows

namespace OAI

/-!
# Simultaneous small central portions at both shearing radii

This combines the two exponential regimes, all four candidate windows,
and the actual leaf scaling law. It proves the leaf-mass conclusion of
EKL Lemma 4.6 at the inverse shearing scale and at a fixed enlargement,
for both initial points, at one common recurrence time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_synchronized_leaf_annuli
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (g : G (d + 1))
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (hT : 1 ≤ rootShearingLogTime i j g)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g)
    (G H : Set (X (d + 1))) (z : Fin 2 → X (d + 1))
    (ρ ε : ℝ) (a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z k) (Metric.ball 0 r))
    (heq : intrinsicRootKernel hij μ hfree (z 0) = intrinsicRootKernel hij μ hfree (z 1))
    (hcov : ∀ k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z k) t)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 (rootShearingLogTime i j g),
      let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
      let r := fun b : Fin 2 => (if b = 0 then 1 else C) *
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹
      (∀ k, x k ∈ G) ∧
      intrinsicRootKernel hij μ hfree (x 0) = intrinsicRootKernel hij μ hfree (x 1) ∧
      (∀ b, 0 < r b) ∧
      ∀ k b, intrinsicRootKernel hij μ hfree (x k) (Metric.closedBall 0 (ρ * r b)) <
        a * intrinsicRootKernel hij μ hfree (x k) (Metric.closedBall 0 (r b)) := by
  obtain ⟨θ, η, hθlo, hθhi, hη, hreg⟩ :=
    rootShearing_four_candidate_windows hij g hnot hsmall C hC hlog
  obtain ⟨τ, hτ, hg, hh⟩ := exists_common_four_window_time_with_covariance
    (fun t x => rightAction x (rootPairFlow i j (-t))) G H z
    (rootShearingLogTime i j g) ε (by linarith) hε θ η hθlo hθhi hη
    (fun k => (hcontrol k _ hT).1)
    (fun k => (hcontrol k _ (by linarith)).2)
    (RootPairLeafCovariance hij μ hfree) hcov
  obtain ⟨mode, hmode⟩ := hreg τ ⟨hτ.1.le, hτ.2⟩
  refine ⟨τ, hτ, fun k => (hg k).1, ?_, ?_, ?_⟩
  · have h0 := (hg 0).2
    have h1 := (hg 1).2
    change intrinsicRootKernel hij μ hfree _ = rootPairCovarianceKernel hij μ hfree _ at h0 h1
    rw [h0, h1, rootPairCovarianceKernel_apply, rootPairCovarianceKernel_apply, heq]
  · intro b
    dsimp only
    rw [hmode b]
    exact Real.exp_pos _
  · intro k b
    let v := (θ (mode, b) + (2 - η (mode, b)) * τ) / 2
    have hv := (hh k (mode, b)).2
    have hsmall' := hHsmall _ (hh k (mode, b)).1
    have h := rootPair_small_ball_gives_annulus hij μ hfree (z k) τ v ρ a
      (hpos k) (hg k).2 hv hsmall'
    have hr : Real.exp (2 * (v - τ)) =
        (if b = 0 then 1 else C) *
          (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ := by
      rw [hmode b]
      congr 1
      dsimp only [v]
      ring
    simpa only [hr] using h

end DukePrimeDegree

end

end OAI
