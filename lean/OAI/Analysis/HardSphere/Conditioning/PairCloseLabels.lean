import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalCloseLabels

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def pairCloseLabels {m : ℕ} (L : Length) (s : ℝ) (v : Torus L)
    (Y : Configuration m L) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i ↦ torusDistance L (Y i) v≤5 ∧
    ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s)

lemma localCloseLabels_eq_pairCloseLabels {m : ℕ} [Nontrivial (Fin m)]
    (L : Length) (s : ℝ) (v : Torus L) (Y : Configuration m L) :
    localCloseLabels L s v Y=pairCloseLabels L s v Y := by
  classical
  ext i
  simp only [localCloseLabels,pairCloseLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hv,hi⟩
    exact ⟨hv,nearestLabel L Y i,nearestLabel_ne L Y i,hi⟩
  · rintro ⟨hv,j,hji,hj⟩
    exact ⟨hv,(nearestParticleDistance_le L Y i j hji).trans hj⟩

lemma pairCloseLabels_restrict_card_le {m n : ℕ} [Nontrivial (Fin n)]
    (L : Length) (s : ℝ) (v : Torus L) (e : Fin m ↪ Fin n) (X : Configuration n L) :
    (pairCloseLabels L s v (fun i ↦ X (e i))).card≤(localCloseLabels L s v X).card := by
  classical
  have hsub : (pairCloseLabels L s v (fun i ↦ X (e i))).map e⊆localCloseLabels L s v X := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨hv,k,hkj,hk⟩ := (Finset.mem_filter.1 hj).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _,hv,?_⟩
    exact (nearestParticleDistance_le L X (e j) (e k) (fun he ↦ hkj (e.injective he))).trans hk
  simpa only [Finset.card_map] using Finset.card_le_card hsub

attribute [local irreducible] torusDistance nearestParticleDistance

lemma pairCloseLabels_measurable {m : ℕ} (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun Y : Configuration m L ↦ ((pairCloseLabels L s v Y).card:ℝ)) := by
  classical
  simp only [pairCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) v) :=
    (torusDistance_continuous_pair L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration m L ↦ v)))
  have hp : MeasurableSet {Y : Configuration m L | ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    have hc : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) (Y j)) :=
      (torusDistance_continuous_pair L).comp ((show Continuous (fun Y : Configuration m L ↦ Y i) from continuous_apply i).prodMk
        (show Continuous (fun Y : Configuration m L ↦ Y j) from continuous_apply j))
    by_cases hji : j≠i
    · convert measurableSet_le hc.measurable (show Measurable (fun _ : Configuration m L ↦ s) from measurable_const) using 1
      ext Y
      exact and_iff_right hji
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Configuration m L))) using 1
      ext Y
      exact iff_false_intro (fun h ↦ hji h.1)
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter hp)
    measurable_const measurable_const

theorem closeBath_marginal_le {m n : ℕ} [Nontrivial (Fin n)] {S : Type*}
    (L : Length) (s h : ℝ) (e : Fin m ↪ Fin n) (μ : Measure (Configuration n L))
    (v : S → Torus L) (A : Finset S) :
    (μ.map (fun X i ↦ X (e i))) {Y | ∀ a∈A, h≤((pairCloseLabels L s (v a) Y).card:ℝ)}≤
      μ {X | ∀ a∈A, h≤((localCloseLabels L s (v a) X).card:ℝ)} := by
  classical
  have hm : Measurable (fun X : Configuration n L ↦ (fun i : Fin m ↦ X (e i))) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  have hT : MeasurableSet {Y : Configuration m L | ∀ a∈A, h≤((pairCloseLabels L s (v a) Y).card:ℝ)} := by
    simpa only [Set.ofPred_forall] using Finset.measurableSet_biInter A (fun a _ ↦
      measurableSet_le (show Measurable (fun _ : Configuration m L ↦ h) from measurable_const)
        (pairCloseLabels_measurable L s (v a)))
  rw [Measure.map_apply hm hT]
  apply measure_mono
  intro X hX a ha
  exact (hX a ha).trans (by exact_mod_cast pairCloseLabels_restrict_card_le L s (v a) e X)

end HardSphere

end

end OAI
