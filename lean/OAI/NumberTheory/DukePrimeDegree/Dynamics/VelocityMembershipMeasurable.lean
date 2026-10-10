import OAI.NumberTheory.DukePrimeDegree.Dynamics.MatrixExponentialVelocity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelStabilizerMeasurable

namespace OAI

/-!
# Measurable tests for actual component velocities

For a fixed matrix, membership in the velocity space of a component
stabilizer is a measurable event. The exponential characterization makes
it a countable collection of ordinary stabilizer tests. Rational times
suffice because the subgroup and its matrix image are closed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

lemma all_exp_mem_iff_rational_exp_mem {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp (t • V)) ↔
      ∀ q : ℚ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp ((q : ℝ) • V) := by
  constructor
  · exact fun h q => h q
  · intro h t
    have himage : IsClosed ((fun g : G n => g.val) '' (L : Set (G n))) :=
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.isClosedMap _ hL
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp (t • V)) :=
      (differentiable_exp_smul_const ℝ V).continuous
    have hclosed := himage.preimage hcont
    have hrat : ∀ q : ℚ, NormedSpace.exp ((q : ℝ) • V) ∈
        (fun g : G n => g.val) '' (L : Set (G n)) := by
      intro q
      obtain ⟨g, hg, he⟩ := h q
      exact ⟨g, hg, he⟩
    exact Rat.denseRange_cast.induction_on t hclosed hrat

lemma mem_matrixVelocitySpace_iff_rational_exp {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    V ∈ matrixVelocitySpace L ↔
      ∀ q : ℚ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp ((q : ℝ) • V) :=
  (mem_matrixVelocitySpace_iff_exp L hL V).trans
    (all_exp_mem_iff_rational_exp_mem L hL V)

private lemma measurableSet_kernel_exp_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (κ : Kernel Z (X n)) [IsFiniteKernel κ]
    (M : Matrix (Fin n) (Fin n) ℝ) :
    MeasurableSet {z | ∃ g : G n, g ∈ invariantRightSubgroup (κ z) ∧ g.val = M} := by
  classical
  by_cases hM : ∃ g : G n, g.val = M
  · obtain ⟨g, hg⟩ := hM
    have he : {z | ∃ h : G n, h ∈ invariantRightSubgroup (κ z) ∧ h.val = M} =
        {z | g ∈ invariantRightSubgroup (κ z)} := by
      ext z
      constructor
      · rintro ⟨h, hh, hhM⟩
        have hhe : h = g := Subtype.ext (hhM.trans hg.symm)
        change g ∈ invariantRightSubgroup (κ z)
        simpa only [hhe] using hh
      · intro hz
        exact ⟨g, hz, hg⟩
    rw [he]
    exact measurableSet_kernel_translation_invariant κ g
  · have he : {z | ∃ g : G n, g ∈ invariantRightSubgroup (κ z) ∧ g.val = M} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨g, _, hg⟩
      exact hM ⟨g, hg⟩
    rw [he]
    exact MeasurableSet.empty

/-- This tests the genuine differentiable-curve velocity space. No
measurable choice of subgroup curves is assumed or made. -/
theorem measurableSet_kernel_velocity_mem
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsFiniteKernel κ]
    (V : Matrix (Fin n) (Fin n) ℝ) :
    MeasurableSet {z | V ∈ matrixVelocitySpace (invariantRightSubgroup (κ z))} := by
  have he : {z | V ∈ matrixVelocitySpace (invariantRightSubgroup (κ z))} =
      ⋂ q : ℚ, {z | ∃ g : G n, g ∈ invariantRightSubgroup (κ z) ∧
        g.val = NormedSpace.exp ((q : ℝ) • V)} := by
    ext z
    simp only [mem_iInter, mem_ofPred_eq]
    exact mem_matrixVelocitySpace_iff_rational_exp _ (isClosed_invariantRightSubgroup (κ z)) V
  rw [he]
  exact MeasurableSet.iInter fun q => measurableSet_kernel_exp_invariant κ _

end DukePrimeDegree

end

end OAI
