import OAI.GroupTheory.PolycyclicRecognition.Algebra.EigenlineCones
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # Small cones around different lines are disjoint -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_positive_interval_lt (f : ℝ → ℝ) (hf : ContinuousAt f 0)
    (c : ℝ) (hc : f 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → f t < c := by
  have he : ∀ᶠ t in nhds (0 : ℝ), f t < c := hf.eventually (gt_mem_nhds hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, fun t ht htε => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]
  linarith

theorem small_eigenline_cones_disjoint [FiniteDimensional ℝ V]
    (φ ψ : V →L[ℝ] ℝ) (v w : V)
    (hw : w ∉ Submodule.span ℝ ({v} : Set V)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε →
      Disjoint (eigenlineCone φ v t) (eigenlineCone ψ w t) := by
  obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  let θ := f.toContinuousLinearMap
  have hθv : θ v = 0 := by
    have hh : f v ∈ (Submodule.span ℝ ({v} : Set V)).map f :=
      ⟨v, Submodule.subset_span (Set.mem_singleton v), rfl⟩
    rw [hf, Submodule.mem_bot] at hh
    exact hh
  have hθw : θ w ≠ 0 := hfw
  let p : ℝ → ℝ := fun t => (‖θ‖ * t) * (|φ w| + ‖φ‖ * t) + ‖θ‖ * t
  have hp : ContinuousAt p 0 := by fun_prop
  obtain ⟨ε, hε, hεp⟩ := exists_positive_interval_lt p hp |θ w| (by
    simpa only [p, mul_zero, zero_mul, add_zero] using abs_pos.mpr hθw)
  refine ⟨ε, hε, fun t ht htε => eigenline_cones_disjoint_of_separator φ ψ θ v w t hθv ?_⟩
  have hh := hεp t ht htε
  dsimp only [p] at hh
  linarith

end PolycyclicRecognition

end

end OAI
