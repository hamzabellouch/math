import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarChildMaximum
import OAI.MeasureTheory.FalconerCompletion.Graphs.ResidualAngular

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal Topology Classical
variable {n : ℕ}

lemma policyDescriptor_anchor_gt_start (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0<q) {b : PolicyDescriptor} (hb : b∈policyDescriptorList A N q a t) :
    a<descriptorAnchor b := by
  obtain ⟨z,hz,hb⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨hz,ha,ht,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2≤N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  rw [originDescriptor_anchor A hb]
  have hp := (policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)).1
  omega

lemma policyDescriptorList_subset_unreached
    (A : ℕ → ℝ) {N q a₀ t₀ a b t : ℕ} (hq : 0<q)
    (ha : a₀≤a) (hab : a<b) (ht : t≤t₀) :
    policyDescriptorList A N q b t ⊆ unreachedDescriptorList A N q a₀ t₀ a := by
  intro e he
  exact Finset.mem_filter.mpr ⟨policyDescriptorList_mono A (ha.trans hab.le) ht he,
    hab.trans (policyDescriptor_anchor_gt_start A hq he)⟩

lemma actualResidualAmbientGood_subset_farChild
    (A : ℕ → ℝ) {N q a₀ t₀ a b t : ℕ} (hq : 0<q)
    (ha : a₀≤a) (hab : a<b) (ht : t≤t₀)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ)
    (sig C : ℝ) (J i : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    actualResidualAmbientGood A N q a₀ t₀ a ρ m sig C J i x ⊆
      actualPolicyAmbientGood A N q b t ρ m sig C J i x := by
  intro w hw
  rcases hw with hw | hw
  · exact Or.inl hw
  · exact Or.inr (fun e he => hw e (policyDescriptorList_subset_unreached A hq ha hab ht he))

lemma actualResidualPairAmbientGood_subset_farChild
    (A : ℕ → ℝ) {N q a₀ t₀ a b t : ℕ} (hq : 0<q)
    (ha : a₀≤a) (hab : a<b) (ht : t≤t₀)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ)
    (sig C : ℝ) (J i : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1))) :
    actualResidualPairAmbientGood A N q a₀ t₀ a ρ m sig C J i z ⊆
      actualPairAmbientGood A N q b t ρ m sig C J i z := by
  intro w hw
  exact ⟨actualResidualAmbientGood_subset_farChild A hq ha hab ht ρ m sig C J i z.1 hw.1,
    actualResidualAmbientGood_subset_farChild A hq ha hab ht ρ m sig C J i z.2 hw.2⟩

lemma positiveDistanceCountND_mono
    {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V]
    (μ ν : Measure (V×V)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ≤ν) (d : ℕ) (v a M : ℝ) :
    positiveDistanceCountND μ d v a M ≤ positiveDistanceCountND ν d v a M := by
  exact mul_le_mul' le_rfl ((Measure.prod_mono hμ hμ) _)

lemma farChildMaximumND_mono
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ)×(Fin (n+1) → ℤ))) (v M : ℝ)
    (U V U' V' : (EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1))))
    (hU : ∀ z, U z⊆U' z) (hV : ∀ z, V z⊆V' z) :
    farChildMaximumND ρ κ a P Q v M U V ≤ farChildMaximumND ρ κ a P Q v M U' V' := by
  apply sup_le_sup
  · apply Finset.sup_mono_fun
    intro p hp
    exact positiveDistanceCountND_mono
      ((gridPairMeasureND ρ a p).restrict {z | euclideanPairDirectionND z∈U z})
      ((gridPairMeasureND ρ a p).restrict {z | euclideanPairDirectionND z∈U' z})
      (Measure.restrict_mono (fun z hz => hU z hz) le_rfl) _ _ _ _
  · apply Finset.sup_mono_fun
    intro p hp
    exact positiveDistanceCountND_mono
      ((gridPairMeasureND κ a p).restrict {z | euclideanPairDirectionND z∈V z})
      ((gridPairMeasureND κ a p).restrict {z | euclideanPairDirectionND z∈V' z})
      (Measure.restrict_mono (fun z hz => hV z hz) le_rfl) _ _ _ _

lemma actualResidual_farChildMaximum_le
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (A : ℕ → ℝ) {N q a₀ t₀ a b t : ℕ} (hq : 0<q)
    (ha : a₀≤a) (hab : a<b) (ht : t≤t₀)
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (P Q : Finset ((Fin (n+1) → ℤ)×(Fin (n+1) → ℤ))) (v M : ℝ) :
    farChildMaximumND ρ κ b P Q v M
      (actualResidualPairAmbientGood A N q a₀ t₀ a ρ m sig C J i)
      (actualResidualPairAmbientGood A N q a₀ t₀ a κ m sig C J i) ≤
    farChildMaximumND ρ κ b P Q v M
      (actualPairAmbientGood A N q b t ρ m sig C J i)
      (actualPairAmbientGood A N q b t κ m sig C J i) :=
  farChildMaximumND_mono ρ κ b P Q v M _ _ _ _
    (actualResidualPairAmbientGood_subset_farChild A hq ha hab ht ρ m sig C J i)
    (actualResidualPairAmbientGood_subset_farChild A hq ha hab ht κ m sig C J i)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
