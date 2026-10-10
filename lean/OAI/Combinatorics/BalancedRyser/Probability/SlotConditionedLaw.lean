import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.BalancedRyser.Probability.SlotEdges2

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace Balanced.Slots

universe u v
variable {ι : Type u} {V : ι → Type v}
variable [Fintype ι] [∀ i, Fintype (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

theorem conditional_law_eq_uniformOn (G : Set (Assignment V)) :
    cond (law V) G = uniformOn G := by
  rw [law_eq_uniformOn]
  unfold uniformOn
  rw [cond_cond_eq_cond_inter MeasurableSet.univ (Set.toFinite G).measurableSet]
  simp

theorem conditional_law_eq_uniformOfFinset (G : Finset (Assignment V))
    (hG : G.Nonempty) :
    cond (law V) (G : Set (Assignment V)) = (PMF.uniformOfFinset G hG).toMeasure := by
  classical
  rw [conditional_law_eq_uniformOn]
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
    PMF.uniformOfFinset_apply]
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases ha : a ∈ G <;> simp [ha]

theorem conditional_law_real_finset (G A : Finset (Assignment V)) :
    (cond (law V) (G : Set (Assignment V))).real (A : Set (Assignment V)) =
      ((G ∩ A).card : ℝ) / (G.card : ℝ) := by
  classical
  rw [conditional_law_eq_uniformOn]
  simp [Measure.real, uniformOn_apply_finset, ENNReal.toReal_div]

theorem conditional_law_real_singleton (G : Finset (Assignment V))
    (hG : G.Nonempty) (a : Assignment V) :
    (cond (law V) (G : Set (Assignment V))).real {a} =
      if a ∈ G then (G.card : ℝ)⁻¹ else 0 := by
  classical
  rw [conditional_law_eq_uniformOfFinset G hG]
  by_cases ha : a ∈ G <;> simp [Measure.real, PMF.uniformOfFinset_apply, ha]

theorem sum_conditional_law_real_singleton (G : Finset (Assignment V))
    (hG : G.Nonempty) :
    ∑ a : Assignment V, (cond (law V) (G : Set (Assignment V))).real {a} = 1 := by
  classical
  have hc : (G.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hG
  simp [conditional_law_real_singleton G hG, Finset.sum_ite_mem, hc]

theorem conditional_law_real_singleton_pos_iff (G : Finset (Assignment V))
    (hG : G.Nonempty) (a : Assignment V) :
    0 < (cond (law V) (G : Set (Assignment V))).real {a} ↔ a ∈ G := by
  classical
  rw [conditional_law_real_singleton G hG]
  have hc : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  by_cases ha : a ∈ G <;> simp [ha, inv_pos.mpr hc]

variable [∀ i, Nonempty (V i)]

theorem law_real_pos_iff_nonempty (G : Finset (Assignment V)) :
    0 < (law V).real (G : Set (Assignment V)) ↔ G.Nonempty := by
  classical
  rw [law_real_finset]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (0 : ℝ) < Fintype.card (Assignment V) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    by_contra hn
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he] at h
  · intro h
    exact mul_pos (by exact_mod_cast h.card_pos) (inv_pos.mpr hc)

end Balanced.Slots

end

end OAI
