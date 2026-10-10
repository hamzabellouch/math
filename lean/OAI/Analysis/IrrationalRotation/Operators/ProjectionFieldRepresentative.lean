import OAI.Analysis.IrrationalRotation.Model.CompactTransfer
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Fields

theorem exists_everywhere_projection_field
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ᵐ x ∂μ, IsStarProjection (P x))
    (hm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1))) :
    ∃ Q : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ,
      (∀ x, IsStarProjection (Q x)) ∧
      (∀ k : ℤ, Measurable (fun x => Q x (lp.single 2 k 1))) ∧
      Q =ᵐ[μ] P := by
  classical
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  let Q : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ :=
    fun x => if x ∈ N then 0 else P x
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ N
    · simpa only [Q, ite_eq_left hx] using IsStarProjection.zero
        (SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    · simp only [Q, ite_eq_right hx]
      by_contra h
      exact hx (hsub h)
  · intro k
    have h : Measurable (fun x => if x ∈ N then (0 : SequenceHilbert ℤ)
        else P x (lp.single 2 k 1)) :=
      Measurable.ite hN measurable_const (hm k)
    convert h using 1
    funext x
    by_cases hx : x ∈ N <;> simp [Q, hx]
  · filter_upwards [show ∀ᵐ x ∂μ, x ∉ N from ae_iff.mpr (by simpa using hnull)] with x hx
    simp only [Q, ite_eq_right hx]

end Invariant233.Fields

end

end OAI
