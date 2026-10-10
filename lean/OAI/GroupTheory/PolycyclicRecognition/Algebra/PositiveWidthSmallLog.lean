import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledBasisScaleChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentSectionRemainder
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Short metric factors fit inside every positive-width ordinary box -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

/-- A sufficiently small exponential-in-distance logarithmic bound fits
inside the unit box at the ambient scale. The permitted distance fraction
is fixed uniformly over all large scales and all logarithms. -/
theorem exists_small_distance_exponential_box
    {L N J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (Exp : L → N)
    {lo C A : ℝ} (hlo : 0 < lo) (hcost : ∀ j, lo ≤ cost j)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (q : ℕ) :
    ∃ η S : ℝ, 0 < η ∧ η ≤ 1 ∧ 1 ≤ S ∧
      ∀ r : ℝ, S ≤ r → ∀ a : ℝ, 0 ≤ a → a ≤ η * r → ∀ v : L,
      ‖b.equivFun v‖ ≤ C * (3 + a) ^ q * Real.exp (A * (a + 1)) →
      Exp v ∈ exponentialCoordinateBox Exp (exponentialRescaleBasis b cost r) 1 := by
  let η := min 1 (lo / (2 * (A + 1)))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hlo (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hAη : A * η ≤ lo / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp
      (min_le_right 1 (lo / (2 * (A + 1))))
    change η * (2 * (A + 1)) ≤ lo at hh
    nlinarith
  let P := (C + 1) * Real.exp A * 3 ^ q
  have hP : 0 < P := by dsimp [P]; positivity
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp
    (subexponential_upper_polynomial hP q (lo / 2) (half_pos hlo))
  refine ⟨η, max 1 S₀, hη, hη1, le_max_left _ _, ?_⟩
  intro r hr a ha har v hv
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 ≤ r := by linarith
  have hpoly := hS₀ r ((le_max_right _ _).trans hr)
  have hbase : 3 + a ≤ 3 * (1 + r) := by
    have := har.trans (mul_le_of_le_one_left hr0 hη1)
    linarith
  have hexp : Real.exp (A * (a + 1)) ≤ Real.exp A * Real.exp (A * η * r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left har hA]
  have hsmall : ‖b.equivFun v‖ ≤ P * (1 + r) ^ q * Real.exp (A * η * r) := by
    apply hv.trans
    calc
      _ ≤ C * (3 * (1 + r)) ^ q * (Real.exp A * Real.exp (A * η * r)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith) hbase q) hC) hexp
          (Real.exp_nonneg _) (by positivity)
      _ ≤ P * (1 + r) ^ q * Real.exp (A * η * r) := by
        dsimp [P]
        rw [mul_pow]
        nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ 1 + r) q)
          (mul_nonneg (Real.exp_nonneg A) (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) q)
            (Real.exp_nonneg (A * η * r))))]
  refine ⟨v, rfl, ?_⟩
  have hb := norm_scale_exponentialRescaleBasis_le b cost r 0 (-lo * r)
    (fun j => by nlinarith [mul_le_mul_of_nonneg_left (hcost j) hr0]) v
  rw [exponentialRescaleBasis_zero] at hb
  calc
    _ ≤ Real.exp (-lo * r) * (P * (1 + r) ^ q * Real.exp (A * η * r)) :=
      hb.trans (mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _))
    _ = (P * (1 + r) ^ q) * Real.exp ((A * η - lo) * r) := by
      rw [show (A * η - lo) * r = -lo * r + A * η * r by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (lo / 2 * r) * Real.exp (-(lo / 2) * r) := by
      exact mul_le_mul hpoly (Real.exp_le_exp.mpr (by nlinarith))
        (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

end PolycyclicRecognition

end

end OAI
