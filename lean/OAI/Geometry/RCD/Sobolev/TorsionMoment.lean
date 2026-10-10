import OAI.Geometry.RCD.Sobolev.LevelTruncation
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-!
# Moment estimates for the torsion superlevel test

Hölder is applied to a bounded two-level truncation and the indicator of its
support. The resulting algebraic estimate is the nonlinear gain needed by
the superlevel iteration.
-/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

/-- Hölder for a bounded nonnegative function supported on a measurable set. -/
theorem bounded_support_integral_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {v : X → ℝ} (hv : AEMeasurable v ν)
    {M p q : ℝ} (hpq : p.HolderConjugate q)
    (hb : ∀ᵐ x ∂ν, 0 ≤ v x ∧ v x ≤ M)
    (S : Set X) (hS : MeasurableSet S) (hz : ∀ᵐ x ∂ν, x ∉ S → v x = 0) :
    (∫ x, v x ∂ν) ≤ (∫ x, v x ^ p ∂ν) ^ (1 / p) * (ν.real S) ^ (1 / q) := by
  let g : X → ℝ := S.indicator (fun _ => 1)
  have hm : MemLp v (ENNReal.ofReal p) ν := MemLp.of_bound hv.aestronglyMeasurable M
    (hb.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  have hgm : Measurable g := measurable_const.indicator hS
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    by_cases hx : x ∈ S <;> simp [g, hx]
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    by_cases hx : x ∈ S <;> simp [g, hx]
  have hgmLp : MemLp g (ENNReal.ofReal q) ν :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hmul : (fun x => v x * g x) =ᵐ[ν] v := by
    filter_upwards [hz] with x hx
    by_cases hm : x ∈ S
    · simp [g, hm]
    · simp [g, hm, hx hm]
  have hgpow : (fun x => g x ^ q) = g := by
    funext x
    by_cases hx : x ∈ S
    · simp [g, hx]
    · simp [g, hx, Real.zero_rpow hpq.symm.pos.ne']
  have hgi : (∫ x, g x ^ q ∂ν) = ν.real S := by
    rw [hgpow]
    simp only [g, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (hb.mono fun _ hx => hx.1)
    (Eventually.of_forall hg0) hm hgmLp
  rw [integral_congr_ae hmul, hgi] at hh
  exact hh

/-- The scalar gain after combining Sobolev with the supported Hölder bound. -/
theorem moment_le_of_sobolev_holder {I C Y p : ℝ}
    (hI : 0 ≤ I) (hC : 0 ≤ C) (hY : 0 ≤ Y) (hp : 1 < p)
    (hbound : I ^ (2 / p) ≤ C * (I ^ (1 / p) * Y ^ ((p - 1) / p))) :
    I ≤ C ^ p * Y ^ (p - 1) := by
  let Z := I ^ (1 / p)
  have hZ : 0 ≤ Z := Real.rpow_nonneg hI _
  have hZsq : Z ^ 2 = I ^ (2 / p) := by
    dsimp [Z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
    congr 1
    ring
  have hZi : Z ^ p = I := by
    dsimp [Z]
    rw [← Real.rpow_mul hI]
    simp only [one_div, inv_mul_cancel₀ (by linarith : p ≠ 0), Real.rpow_one]
  have hzle : Z ≤ C * Y ^ ((p - 1) / p) := by
    have hh : Z ^ 2 ≤ C * (Z * Y ^ ((p - 1) / p)) := hZsq ▸ hbound
    by_cases hz : Z = 0
    · rw [hz]
      exact mul_nonneg hC (Real.rpow_nonneg hY _)
    · nlinarith [lt_of_le_of_ne hZ (Ne.symm hz)]
  have hh := Real.rpow_le_rpow hZ hzle (by linarith : 0 ≤ p)
  rw [hZi, Real.mul_rpow hC (Real.rpow_nonneg hY _), ← Real.rpow_mul hY] at hh
  convert hh using 1
  congr 2
  field_simp

end RegularPointCoordinates

end

end OAI
