import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentWordMetric

namespace OAI

/-! # Vanishing normalized coordinates give sublinear metric displacement -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Shifting the logarithmic scale changes each coordinate by one fixed
factor. This identity does not require the costs to be positive. -/
theorem repr_shift_exponentialRescaleBasis
    (b : Basis J ℝ L) (cost : J → ℝ) (r a : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b cost (r + a)).repr x j =
      Real.exp (-a * cost j) * (exponentialRescaleBasis b cost r).repr x j := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- All coordinates obey one common bound for a fixed shift. -/
theorem norm_shift_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (r a : ℝ) (x : L) :
    ‖(exponentialRescaleBasis b cost (r + a)).equivFun x‖ ≤
      (∑ j, Real.exp (-a * cost j)) * ‖(exponentialRescaleBasis b cost r).equivFun x‖ := by
  have hc : 0 ≤ ∑ j, Real.exp (-a * cost j) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b cost (r + a)).repr x j| ≤ _
  rw [repr_shift_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul
    (Finset.single_le_sum (f := fun i => Real.exp (-a * cost i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j))
    (norm_le_pi_norm ((exponentialRescaleBasis b cost r).equivFun x) j)
    (abs_nonneg _) hc

/-- A unit-chart metric estimate at every large scale implies that every
sequence with normalized coordinates tending to zero has sublinear length.
The proof uses a fixed smaller scale before passing to the limit. -/
theorem metric_sublinear_of_rescaled_coordinates_tendsto_zero
    {G ι : Type*} [Group G] [PseudoMetricSpace G] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (Exp : L → G)
    {C : ℝ} (_hC : 0 ≤ C)
    (hmetric : ∀ s : ℝ, 0 ≤ s → ∀ x : L,
      ‖(exponentialRescaleBasis b cost s).equivFun x‖ ≤ 1 →
        dist 1 (Exp x) ≤ C * Real.exp s)
    {l : Filter ι} (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (x : ι → L)
    (hsmall : Tendsto (fun i => (exponentialRescaleBasis b cost (scale i)).equivFun (x i))
      l (𝓝 0)) :
    Tendsto (fun i => dist 1 (Exp (x i)) / Real.exp (scale i)) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun i => ha.trans_le (by positivity))
  · intro ε hε
    have hexp := Real.tendsto_exp_atBot.const_mul C
    simp only [mul_zero] at hexp
    obtain ⟨a, ha⟩ := (hexp.eventually (eventually_lt_nhds hε)).exists
    let B := ∑ j, Real.exp (-a * cost j)
    have hsmall' : Tendsto (fun i => B *
        ‖(exponentialRescaleBasis b cost (scale i)).equivFun (x i)‖) l (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using hsmall.norm.const_mul B
    filter_upwards [hscale.eventually (eventually_ge_atTop (-a)),
      hsmall'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hs
    have hcoord : ‖(exponentialRescaleBasis b cost (scale i + a)).equivFun (x i)‖ ≤ 1 :=
      (norm_shift_exponentialRescaleBasis_le b cost (scale i) a (x i)).trans hs.le
    have hm := hmetric (scale i + a) (by linarith) (x i) hcoord
    calc
      dist 1 (Exp (x i)) / Real.exp (scale i) ≤
          (C * Real.exp (scale i + a)) / Real.exp (scale i) := by gcongr
      _ = C * Real.exp a := by rw [Real.exp_add]; field_simp
      _ < ε := ha

end PolycyclicRecognition

end

end OAI
