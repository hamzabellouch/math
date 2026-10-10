import OAI.MeasureTheory.Falconer.Estimates.TestWidths
import OAI.MeasureTheory.Falconer.Estimates.ConditionalCollision
import OAI.MeasureTheory.Falconer.Geometry.ConditionalProjectionTest
import OAI.MeasureTheory.Falconer.Estimates.ParallelGood
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

def descriptorValid (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p t => p ≤ t ∧ t ≤ N

noncomputable def descriptorGoodDirections (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (P : List (Fin d → Bool)) :
    PolicyDescriptor → Set (Sphere d)
  | .parallel g p => Regularization.parallelGoodSet Q ρ g p P (angularTestWidth N σ J i p)
      (((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ))
  | .projection p t => Regularization.conditionalProjectionGoodSet Q ρ P
      (angularTestWidth N σ J i t)
      ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
        Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))

theorem descriptorGoodDirections_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (P : List (Fin d → Bool)) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodDirections Q ρ m N σ J i P b) := by
  cases b with
  | parallel g p => exact Regularization.parallelGoodSet_measurable _ _ _ _ _ _ _
  | projection p t => exact Regularization.conditionalProjectionGoodSet_measurable _ _ _ _ _

theorem descriptor_projection_original_bound (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i p t : ℕ)
    (P : List (Fin d → Bool)) (w : Sphere d)
    (hw : w ∈ descriptorGoodDirections Q ρ m N σ J i P (.projection p t)) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Space d × Space d | |inner ℝ (w:Space d) (z.1-z.2)| ≤ angularTestWidth N σ J i t} ≤
      ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
        Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) *
          (ρ (Q.descendant P).carrier)^2 := by
  classical
  unfold descriptorGoodDirections Regularization.conditionalProjectionGoodSet at hw
  split_ifs at hw with hocc
  · exact conditional_projection_to_restriction ρ _ hocc.ne' _ _ hw
  · exact False.elim hw

theorem uniform_descriptor_direction_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (P : List (Fin d → Bool)), P.length = descriptorAnchor b →
      ∀ (i : ℕ) (w u : Sphere d),
        dist w u ≤ C*angularTestRadius N σ (descriptorLength b) →
        w ∈ descriptorGoodDirections Q ρ m N σ J i P b →
        u ∈ descriptorGoodDirections Q ρ m N σ J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_angularTestWidth_gap hσ hJ
    (20*((d:ℝ)+1)*C) (by positivity)
  obtain ⟨N₂,h₂⟩ := uniform_angularTestWidth_gap hσ hJ
    (Real.sqrt d*C) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m b hb P hP i w u hwu hw
  cases b with
  | parallel g p =>
    apply Regularization.parallelGoodSet_buffer Q ρ g p P
      (mul_nonneg hC (angularTestRadius_pos N σ (p-g)).le) ?_ hw hwu
    convert h₁ N ((le_max_left _ _).trans hN) g p hb.1 i using 1; ring
  | projection p t =>
    apply Regularization.conditionalProjectionGoodSet_buffer Q hQ ρ P
      (mul_nonneg hC (angularTestRadius_pos N σ (t-p)).le)
      (by simpa only [dist_comm, descriptorLength] using hwu) ?_ hw
    have hh := h₂ N ((le_max_right _ _).trans hN) p t hb.1 i
    dsimp only [descriptorAnchor] at hP
    rw [hP]
    convert hh using 1; ring

theorem policy_descriptor_valid (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {b : PolicyDescriptor}
    (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) : descriptorValid N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,descriptorValid] at hpos hbound ⊢ <;>
    omega

end Falconer

end OAI
