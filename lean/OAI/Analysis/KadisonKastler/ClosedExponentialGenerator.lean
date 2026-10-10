import OAI.Analysis.KadisonKastler.ExponentialRemainder
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! # Recovering a small exponential generator in a closed subalgebra

The radius is absolute, independent of the ambient complex Banach algebra.
This is the logarithm-series step needed for a small exact normalizer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped NNReal Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
@[simp] theorem exponentialRemainder_zero : exponentialRemainder (0 : A) = 0 := by
  simp [exponentialRemainder]

theorem norm_exponentialRemainder_le_third {x : A} (hx : ‖x‖ ≤ 1 / 4) :
    ‖exponentialRemainder x‖ ≤ (1 / 3 : ℝ) * ‖x‖ := by
  have h := norm_exponentialRemainder_sub_le x (0 : A)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hx (by simp)
  norm_num at h
  exact h

/-- A small element belongs to every closed complex subalgebra containing its
exponential. The contraction argument supplies a uniform inverse radius. -/
theorem mem_closedSubalgebra_of_exp_mem (S : Subalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (x : A) (hx : ‖x‖ ≤ 1 / 16)
    (hexp : NormedSpace.exp x ∈ S) : x ∈ S := by
  let s : Set A := Metric.closedBall 0 (1 / 4)
  have hs : IsClosed s := Metric.isClosed_closedBall
  let _ : CompleteSpace s := hs.completeSpace_coe
  have hzero : (0 : A) ∈ s := by simp [s]
  let _ : Nonempty s := ⟨⟨0, hzero⟩⟩
  have hx' : ‖x‖ ≤ 1 / 4 := by linarith
  have hexpNorm : ‖NormedSpace.exp x - 1‖ ≤ 1 / 12 := by
    have he : NormedSpace.exp x - 1 = exponentialRemainder x + x := by
      simp [exponentialRemainder]
    rw [he]
    have h := norm_exponentialRemainder_le_third hx'
    exact (norm_add_le _ _).trans (by linarith)
  let f : A → A := fun y => (NormedSpace.exp x - 1) - exponentialRemainder y
  have hfmem {y : A} (hy : y ∈ s) : f y ∈ s := by
    have hyn : ‖y‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using hy
    have hr := norm_exponentialRemainder_le_third hyn
    have hn : ‖f y‖ ≤ 1 / 4 := (norm_sub_le _ _).trans (by linarith)
    simpa [s, dist_eq_norm] using hn
  let F : s → s := fun y => ⟨f y, hfmem y.property⟩
  have hF : ContractingWith (1 / 3 : ℝ≥0) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro y z
    have hyn : ‖(y : A)‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using y.property
    have hzn : ‖(z : A)‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using z.property
    have h := norm_exponentialRemainder_sub_le (y : A) (z : A)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hyn hzn
    change dist (f y) (f z) ≤ (↑(1 / 3 : ℝ≥0)) * dist (y : A) (z : A)
    rw [dist_eq_norm]
    have he : f y - f z = -(exponentialRemainder (y : A) - exponentialRemainder (z : A)) := by
      dsimp [f]
      abel
    rw [he, norm_neg]
    norm_num [dist_eq_norm] at h ⊢
    exact h
  have hxs : x ∈ s := by simpa [s, dist_eq_norm] using hx'
  let X : s := ⟨x, hxs⟩
  have hX : Function.IsFixedPt F X := by
    apply Subtype.ext
    change (NormedSpace.exp x - 1) - exponentialRemainder x = x
    simp [exponentialRemainder]
  have hlim : Tendsto (fun n : ℕ => ((F^[n] ⟨0, hzero⟩ : s) : A)) atTop (𝓝 x) := by
    have h := (continuous_subtype_val.tendsto (ContractingWith.fixedPoint F hF)).comp
      (hF.tendsto_iterate_fixedPoint ⟨0, hzero⟩)
    rw [← hF.fixedPoint_unique hX] at h
    exact h
  have hremain : ∀ n : ℕ, ((F^[n] ⟨0, hzero⟩ : s) : A) ∈ S := by
    intro n
    induction n with
    | zero => exact S.zero_mem
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change f ((F^[n] ⟨0, hzero⟩ : s) : A) ∈ S
      apply S.sub_mem (S.sub_mem hexp S.one_mem)
      apply S.sub_mem (S.sub_mem ?_ S.one_mem) ih
      let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
      exact NormedSpace.exp_mem (R := ℂ) (s := S) hS ih
  exact hS.mem_of_tendsto hlim (Filter.Eventually.of_forall hremain)

end

end KadisonKastler

end OAI
