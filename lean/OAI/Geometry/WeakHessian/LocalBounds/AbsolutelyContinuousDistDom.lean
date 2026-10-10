import Mathlib
import OAI.Geometry.WeakHessian.Transport.ActionIntervalIntegrable

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessianCalculus

lemma absolutelyContinuous_of_dist_dom {f g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ s ∈ Set.uIcc a b, ∀ t ∈ Set.uIcc a b,
      dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hsmall => lt_of_le_of_lt ?_ (hbound E hE hsmall)⟩
  refine Finset.sum_le_sum fun i hi => ?_
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

lemma exists_ac_representative {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1)
    (hbound : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |q (d j) - q (d i)| ≤ ∫⁻ t in Icc (d i : ℝ) (d j : ℝ), a t) :
    ∃ q' : ℝ → ℝ, AbsolutelyContinuousOnInterval q' 0 1 ∧
      ∀ i, q' (d i) = q (d i) := by
  classical
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hdom : ∀ i j, dist (q (d i)) (q (d j)) ≤ dist (A (d i)) (A (d j)) := by
    intro i j
    rcases lt_trichotomy (d i : ℝ) (d j : ℝ) with h|h|h
    · exact action_dist_primitive ha hfin (d i).property (d j).property h.le (hbound i j h)
    · simp only [h, dist_self, le_refl]
    · simpa only [dist_comm] using
        action_dist_primitive ha hfin (d j).property (d i).property h.le (hbound j i h)
  let S : Set ℝ := Set.range (fun i => A (d i))
  let Q : ℝ → ℝ := fun x => if hx : x ∈ S then q (d (Classical.choose hx)) else 0
  have hQ : ∀ i, Q (A (d i)) = q (d i) := by
    intro i
    have hi : A (d i) ∈ S := ⟨i,rfl⟩
    dsimp only [Q]
    rw [dite_eq_left hi]
    apply dist_le_zero.mp
    simpa only [Classical.choose_spec hi, dist_self] using hdom (Classical.choose hi) i
  have hLip : LipschitzOnWith 1 Q S := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    simpa only [hQ, NNReal.coe_one, one_mul] using hdom i j
  obtain ⟨Q',hLip',hEq⟩ := hLip.extend_real
  refine ⟨fun t => Q' (A t), ?_, ?_⟩
  · have hA : AbsolutelyContinuousOnInterval A 0 1 :=
      (action_intervalIntegrable ha hfin).absolutelyContinuousOnInterval_intervalIntegral (by simp)
    apply absolutelyContinuous_of_dist_dom hA
    intro s _ t _
    simpa only [NNReal.coe_one, one_mul] using hLip'.dist_le_mul (A s) (A t)
  · intro i
    exact (hEq ⟨i,rfl⟩).symm.trans (hQ i)

end WeakHessianCalculus

end

end OAI
