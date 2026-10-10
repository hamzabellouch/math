import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SymmetricHeightKernel

namespace OAI

/-!
# Symmetrization of finite fractional height pairings

The distance cutoff defines a measurable, bounded kernel invariant under
swapping its two variables. Applying the symmetric height-kernel identity and
rewriting the cutoff as an indicator identifies the bilinear pairing with an
iterated integral over the closed exterior region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

def symmetricFractionalCutoffKernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  if ε ≤ dist q.1 q.2 then inverseDistancePow (m + 1) q.1 q.2 else 0

theorem symmetricFractionalCutoffKernel_measurable {d : ℕ} (m : ℕ) (ε : ℝ) :
    Measurable (symmetricFractionalCutoffKernel (d := d) m ε) := by
  unfold symmetricFractionalCutoffKernel inverseDistancePow
  apply Measurable.ite (measurableSet_le measurable_const (continuous_fst.dist continuous_snd).measurable)
  · fun_prop
  · exact measurable_const

theorem symmetricFractionalCutoffKernel_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) :
    |symmetricFractionalCutoffKernel m ε q| ≤ (ε ^ (m + 1))⁻¹ := by
  unfold symmetricFractionalCutoffKernel
  split_ifs with h
  · rw [abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    exact inverseDistancePow_bound_of_separation (m + 1) q.1 q.2 ε hε h
  · simp only [abs_zero]
    positivity

theorem symmetricFractionalCutoffKernel_swap {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    symmetricFractionalCutoffKernel m ε q.swap = symmetricFractionalCutoffKernel m ε q := by
  simp only [symmetricFractionalCutoffKernel, Prod.swap, inverseDistancePow, dist_comm q.2 q.1]

theorem finite_fractional_height_pairing_symmetrization {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : Ambient d → ℂ) (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B) :
    (1 / 2 : ℝ) • (∫ q in {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2},
      (w q.1 - w q.2) • (inverseDistancePow (m + 1) q.1 q.2 • (g q.1 - g q.2)) ∂ν.prod ν) =
      ∫ x, w x • (∫ y in closedExterior x ε,
        inverseDistancePow (m + 1) x y • (g x - g y) ∂ν) ∂ν := by
  let k := symmetricFractionalCutoffKernel (d := d) m ε
  have hpair := (finite_symmetric_height_kernel_pairing ν w hwm hw g hgm B hB hg k
    (symmetricFractionalCutoffKernel_measurable m ε) ((ε ^ (m + 1))⁻¹)
    (symmetricFractionalCutoffKernel_bound m ε hε) (symmetricFractionalCutoffKernel_swap m ε)).2
  let S : Set (Ambient d × Ambient d) := {q | ε ≤ dist q.1 q.2}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (continuous_fst.dist continuous_snd).measurable
  have heq : (fun q : Ambient d × Ambient d => (w q.1 - w q.2) • (k q • (g q.1 - g q.2))) =
      S.indicator (fun q => (w q.1 - w q.2) •
        (inverseDistancePow (m + 1) q.1 q.2 • (g q.1 - g q.2))) := by
    funext q
    by_cases h : ε ≤ dist q.1 q.2
    · rw [indicator_of_mem (show q ∈ S from h)]
      simp only [k, symmetricFractionalCutoffKernel, ite_eq_left h]
    · rw [indicator_of_notMem (show q ∉ S from h)]
      simp only [k, symmetricFractionalCutoffKernel, ite_eq_right h]
      exact (congrArg (fun z : ℂ => (w q.1 - w q.2) • z)
        (zero_smul ℝ (g q.1 - g q.2))).trans (smul_zero (w q.1 - w q.2))
  rw [heq, integral_indicator hS] at hpair
  refine hpair.trans (integral_congr_ae (Eventually.of_forall ?_))
  intro x
  apply congrArg (fun z : ℂ => w x • z)
  rw [← integral_indicator (closedExterior_measurable x ε)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  by_cases h : ε ≤ dist x y
  · rw [indicator_of_mem (show y ∈ closedExterior x ε from h)]
    simp only [k, symmetricFractionalCutoffKernel, ite_eq_left h]
  · rw [indicator_of_notMem (show y ∉ closedExterior x ε from h)]
    simp only [k, symmetricFractionalCutoffKernel, ite_eq_right h]
    exact zero_smul ℝ (g x - g y)

end

end RieszRectifiability

end OAI
