import OAI.NumberTheory.DukePrimeDegree.Geometry.SynchronizedAnnuli
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTwoAnnuli

namespace OAI

/-!
# Compact returns in both normalized annuli

The synchronized small central portions and the intrinsic maximal
estimate give simultaneous compact returns at both radii. Multiplying
the chosen times by the shearing scale places them in the two annuli
required by the polynomial noncancellation estimate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_two_normalized_annular_returns
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (hloc : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x))
    (κ ρ C : ℝ) (hκ : 0 < κ) (hC : 1 ≤ C)
    (hsecond : 16 / ρ ≤ ρ * C)
    (hsmall : ∀ b : Fin 2, intrinsicRootLeaf hij μ x
        (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) / κ))) <
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 ((if b = 0 then 1 else C) / κ)))
    (hcoeff : c + c + a < 1) :
    ∃ t : Fin 2 → ℝ,
      (∀ b, rightAction x (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        rightAction y (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K) ∧
      ρ ≤ |κ * t 0| ∧ |κ * t 0| ≤ 1 ∧
      16 / ρ ≤ |κ * t 1| ∧ |κ * t 1| ≤ C := by
  let := hloc
  let r : Fin 2 → ℝ := fun b => (if b = 0 then 1 else C) / κ
  have hr (b : Fin 2) : 0 < r b := by
    apply div_pos _ hκ
    split_ifs
    · norm_num
    · exact zero_lt_one.trans_le hC
  have hmass (b : Fin 2) :
      intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) ≠ 0 := by
    intro he
    have h := hsmall b
    change intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r b)) <
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) at h
    rw [he, mul_zero] at h
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _) h)
  have hfin (b : Fin 2) : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) ≠ ∞ :=
    (isCompact_closedBall (0 : ℝ) (r b)).measure_lt_top.ne
  have hex (b : Fin 2) := exists_annular_simultaneous_root_return hij μ K G c a hgood
    x y hx hy heq (r b) ρ (hr b) (hmass b) (hfin b) (hsmall b).le hcoeff
  choose t hlo hhi hxK hyK using hex
  have hκr (b : Fin 2) : κ * r b = if b = 0 then 1 else C := by
    dsimp only [r]
    field_simp [hκ.ne']
  have hnorm (b : Fin 2) :
      ρ * (if b = 0 then 1 else C) < |κ * t b| ∧
        |κ * t b| ≤ (if b = 0 then 1 else C) := by
    have hl := mul_lt_mul_of_pos_left (hlo b) hκ
    have hu := mul_le_mul_of_nonneg_left (hhi b) hκ.le
    rw [abs_mul, abs_of_pos hκ]
    constructor
    · have hp := congrArg (fun u : ℝ => ρ * u) (hκr b)
      nlinarith
    · linarith [hκr b]
  have hzero : ρ < |κ * t 0| ∧ |κ * t 0| ≤ 1 := by
    simpa only [ite_true, mul_one] using hnorm 0
  have hone : ρ * C < |κ * t 1| ∧ |κ * t 1| ≤ C := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hnorm 1
  exact ⟨t, fun b => ⟨hxK b, hyK b⟩, hzero.1.le, hzero.2,
    hsecond.trans hone.1.le, hone.2⟩

end DukePrimeDegree

end

end OAI
