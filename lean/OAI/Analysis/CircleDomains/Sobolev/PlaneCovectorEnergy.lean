import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The two actual coordinate derivatives control the full covector
energy on the physical plane. No measurability of the covector field
beyond that of the two given derivatives is needed for this bound. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem planeCovector_norm_le (L : EuclideanPlane →L[ℝ] ℝ) :
    ‖L‖ ≤ ‖L (EuclideanSpace.single 0 1)‖ + ‖L (EuclideanSpace.single 1 1)‖ := by
  apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hx : x = (x 0) • EuclideanSpace.single 0 1 + (x 1) • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    ‖L x‖ = ‖(x 0) • L (EuclideanSpace.single 0 1) +
        (x 1) • L (EuclideanSpace.single 1 1)‖ := by
      conv_lhs => rw [hx, map_add, map_smul, map_smul]
    _ ≤ ‖x 0‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x 1‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      simpa only [norm_smul] using norm_add_le
        ((x 0) • L (EuclideanSpace.single 0 1)) ((x 1) • L (EuclideanSpace.single 1 1))
    _ ≤ ‖x‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      gcongr
      · exact PiLp.norm_apply_le x 0
      · exact PiLp.norm_apply_le x 1
    _ = _ := by ring

theorem lintegral_planeCovector_sq_lt_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (L : X → EuclideanPlane →L[ℝ] ℝ)
    (h : ∀ i : Fin 2, MemLp (fun x => L x (EuclideanSpace.single i 1)) 2 μ) :
    (∫⁻ x, ENNReal.ofReal ‖L x‖ ^ 2 ∂μ) < ∞ := by
  let s : X → ℝ := fun x => ‖L x (EuclideanSpace.single 0 1)‖ +
    ‖L x (EuclideanSpace.single 1 1)‖
  have hs : MemLp s 2 μ := (h 0).norm.add (h 1).norm
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hs.eLpNorm_lt_top
  have heq : (fun x => ‖s x‖ₑ ^ (2 : ℝ≥0∞).toReal) =
      (fun x => ENNReal.ofReal (s x) ^ 2) := by
    funext x
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, ENNReal.rpow_two,
      ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq] at hfin
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono
  intro x
  change ENNReal.ofReal ‖L x‖ ^ 2 ≤ ENNReal.ofReal (s x) ^ 2
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (planeCovector_norm_le (L x))) 2

end CircleDomainRigidity

end

end OAI
