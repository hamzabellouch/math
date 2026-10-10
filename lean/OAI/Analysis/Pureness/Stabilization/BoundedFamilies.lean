import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

namespace OAI
noncomputable section
open scoped ENNReal Topology
open Filter
namespace CuntzTrace
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]
abbrev BoundedFamilies := lp A ∞
namespace BoundedFamilies
variable {A}
lemma norm_coordinate_le (x : BoundedFamilies A) (n : ℕ) : ‖x n‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp) x n

def vanishing : Submodule ℂ (BoundedFamilies A) where
  carrier := {x | Tendsto (fun n => ‖x n‖) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' hx hy := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_add_le _ _)
    simpa using hx.add hy
  smul_mem' c x hx := by
    change Tendsto (fun n => ‖c • x n‖) atTop (𝓝 0)
    simpa only [norm_smul, mul_zero] using (tendsto_const_nhds (x := ‖c‖)).mul hx

@[simp] lemma mem_vanishing (x : BoundedFamilies A) : x ∈ vanishing (A := A) ↔
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := Iff.rfl

lemma mul_mem_vanishing_left (x : BoundedFamilies A) {y : BoundedFamilies A}
    (hy : y ∈ vanishing (A := A)) : x*y ∈ vanishing (A := A) := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x‖*‖y n‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ‖x‖)).mul hy
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_right (norm_coordinate_le x n) (norm_nonneg _))

lemma mul_mem_vanishing_right {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A))
    (y : BoundedFamilies A) : x*y ∈ vanishing (A := A) := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x n‖*‖y‖) atTop (𝓝 0) := by
    simpa using hx.mul (tendsto_const_nhds (x := ‖y‖))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_left (norm_coordinate_le y n) (norm_nonneg _))

lemma star_mem_vanishing {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A)) : star x ∈ vanishing (A := A) := by
  change Tendsto (fun n => ‖star (x n)‖) atTop (𝓝 0)
  simpa only [norm_star] using (mem_vanishing x).mp hx

instance vanishing_closed : IsClosed (vanishing (A := A) : Set (BoundedFamilies A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => ‖x n‖) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hdiff : ‖x n-y n‖ < ε/2 := by
    have h := norm_coordinate_le (x-y) n
    exact h.trans_lt (by simpa only [dist_eq_norm] using hxy)
  have htail : ‖y n‖ < ε/2 := by simpa using hN n hn
  rw [dist_zero_right, norm_norm]
  have h : ‖x n‖ ≤ ‖x n-y n‖+‖y n‖ := norm_le_norm_sub_add _ _
  linarith

def vanishingCon : RingCon (BoundedFamilies A) where
  toSetoid := (vanishing (A := A)).quotientRel
  add' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    convert (vanishing (A := A)).add_mem hxy huv using 1
    abel
  mul' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    have h := (vanishing (A := A)).add_mem (mul_mem_vanishing_right hxy u)
      (mul_mem_vanishing_left y huv)
    convert h using 1
    noncomm_ring
end BoundedFamilies
end CuntzTrace

end

end OAI
