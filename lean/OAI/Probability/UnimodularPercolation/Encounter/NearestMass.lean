import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.IntrinsicDistance

namespace OAI

/-! Nearest-vertex transport and its finite incoming mass. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def nearestMass (G : BondGraph V E) (A : Set E → Set V)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ closest (openSimpleGraph G ω) (A ω) x then
    ((closest (openSimpleGraph G ω) (A ω) x).ncard : ℝ≥0∞)⁻¹ else 0

theorem measurable_nearestMass [Countable V] [Countable E]
    (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (x y : V) :
    Measurable (fun ω => nearestMass G A ω x y) := by
  have hm : Measurable (fun ω => closest (openSimpleGraph G ω) (A ω) x) := by
    apply measurable_setOfPred.comp
    apply Measurable.of_eval
    intro z
    exact measurableSet_setOfPred.mp (measurableSet_mem_closest G A hA x z)
  exact Measurable.ite (measurableSet_mem_closest G A hA x y)
    (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_ncard.comp hm)).inv) measurable_const

theorem nearestMass_row_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Set E → Set V) (ω : Set E) (x : V) :
    ∑' y, nearestMass G A ω x y ≤ 1 := by
  let S := closest (openSimpleGraph G ω) (A ω) x
  have hf := closest_finite G hloc ω (A ω) x
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    simp only [nearestMass,ite_eq_right (fun hh => hy (hf.mem_toFinset.mpr hh))])]
  simp only [nearestMass]
  have he : (∑ y ∈ hf.toFinset, if y ∈ S then (S.ncard : ℝ≥0∞)⁻¹ else 0) =
      (S.ncard : ℝ≥0∞) * (S.ncard : ℝ≥0∞)⁻¹ := by
    calc
      _ = ∑ _y ∈ hf.toFinset, (S.ncard : ℝ≥0∞)⁻¹ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [ite_eq_left (hf.mem_toFinset.mp hy)]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf,S]
  change (∑ y ∈ hf.toFinset, if y ∈ S then (S.ncard : ℝ≥0∞)⁻¹ else 0) ≤ 1
  rw [he]
  exact ENNReal.mul_inv_le_one _

theorem nearestMass_aut (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x,
      x ∈ A (b ⁻¹' ω) ↔ a x ∈ A ω)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x y : V) :
    nearestMass G A (b ⁻¹' ω) x y = nearestMass G A ω (a x) (a y) := by
  have heA : A (b ⁻¹' ω) = a ⁻¹' A ω := by ext z; exact hA a b hab ω z
  have heS : closest (openSimpleGraph G (b ⁻¹' ω)) (A (b ⁻¹' ω)) x =
      a ⁻¹' closest (openSimpleGraph G ω) (A ω) (a x) := by
    rw [heA]
    ext z
    exact closest_iso (openAutIso G a b hab ω) (A ω) x z
  simp only [nearestMass,heS,Set.mem_preimage]
  rw [Set.ncard_preimage_of_injective_subset_range a.injective (by simp)]

theorem nearestMass_eq_one (G : BondGraph V E) (A : Set E → Set V)
    (ω : Set E) (x y : V)
    (h : closest (openSimpleGraph G ω) (A ω) x = {y}) :
    nearestMass G A ω x y = 1 := by simp [nearestMass,h]

theorem incoming_top_of_infinite (m : V → ℝ≥0∞) (B : Set V)
    (hB : B.Infinite) (hm : ∀ x ∈ B, m x = 1) : ∑' x, m x = ⊤ := by
  let : Infinite B := hB.to_subtype
  apply top_unique
  calc
    ⊤ = ∑' x : B, (1:ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ = ∑' x : B, m x.val := tsum_congr (fun x => (hm x.val x.property).symm)
    _ = ∑' x, B.indicator m x := tsum_subtype B m
    _ ≤ ∑' x, m x := ENNReal.tsum_le_tsum (fun x => by
      by_cases hx : x ∈ B <;> simp [Set.indicator,hx])

end Percolation

end OAI
