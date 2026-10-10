import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace OAI

/-! Integral payment for all subintervals implies absolute continuity.
The proof compares increments with an absolutely continuous primitive. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma absolutelyContinuous_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  apply lt_of_le_of_lt _ (hbound E hE hlen)
  exact Finset.sum_le_sum fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2

lemma integral_payment_implies_absoluteContinuity {u G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b)
    (hpay : ∀ x y, |u x-u y| ≤ ∫ t in uIoc x y, |G t|) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u a b := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, |G t|
  have hF : AbsolutelyContinuousOnInterval F a b :=
    (hG a b).abs.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  apply absolutelyContinuous_of_dist_le hF
  intro x _ y _
  have he : dist (F x) (F y) = ∫ t in uIoc x y, |G t| := by
    rw [Real.dist_eq, abs_sub_comm]
    change |(∫ t in a..y, |G t|)-(∫ t in a..x, |G t|)| = _
    rw [intervalIntegral.integral_interval_sub_left (hG a y).abs (hG a x).abs,
      intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  rw [he, Real.dist_eq]
  exact hpay x y

end CircleDomainRigidity

end

end OAI
