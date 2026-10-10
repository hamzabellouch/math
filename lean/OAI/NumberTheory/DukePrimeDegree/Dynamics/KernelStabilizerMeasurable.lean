import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

namespace OAI

/-!
# Measurable invariance events for the actual component measures

Equality of finite kernel values is detected by countably many half-line
tests after a measurable embedding in the real line. Consequently both
invariance under one lattice translation and invariance under an entire
root flow are measurable events in the component parameter. The latter
uses rational times and the closedness of the actual measure stabilizer.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_finite_kernel_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [StandardBorelSpace Y] (κ η : Kernel Z Y)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {z | κ z = η z} := by
  let f := embeddingReal Y
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal Y
  let K := κ.map f
  let E := η.map f
  have he (z : Z) : κ z = η z ↔
      K z univ = E z univ ∧ ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ)) := by
    constructor
    · intro hz
      have hz' : K z = E z := by
        simp only [K, E, Kernel.map_apply _ hf.measurable, hz]
      rw [hz']
      exact ⟨rfl, fun _ => rfl⟩
    · rintro ⟨huniv, hq⟩
      apply hf.map_injective
      rw [← Kernel.map_apply κ hf.measurable, ← Kernel.map_apply η hf.measurable]
      change K z = E z
      apply ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat
        Real.isPiSystem_Iic_rat
      · intro s hs
        simp only [mem_iUnion, mem_singleton_iff] at hs
        obtain ⟨q, rfl⟩ := hs
        exact hq q
      · exact huniv
  have huniv : MeasurableSet {z | K z univ = E z univ} :=
    measurableSet_eq_fun (Kernel.measurable_coe K MeasurableSet.univ)
      (Kernel.measurable_coe E MeasurableSet.univ)
  have hhalf : MeasurableSet {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter (fun q : ℚ =>
      measurableSet_eq_fun (Kernel.measurable_coe K (measurableSet_Iic (a := (q : ℝ))))
        (Kernel.measurable_coe E (measurableSet_Iic (a := (q : ℝ)))))
  have hset : {z | κ z = η z} =
      {z | K z univ = E z univ} ∩
        {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    ext z
    exact he z
  rw [hset]
  exact huniv.inter hhalf

lemma measurableSet_kernel_translation_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (κ : Kernel Z (X n)) [IsFiniteKernel κ] (g : G n) :
    MeasurableSet {z | g ∈ invariantRightSubgroup (κ z)} := by
  change MeasurableSet {z | (κ z).map (fun x => rightAction x g) = κ z}
  have h := measurableSet_finite_kernel_eq
    (κ.map (fun x => rightAction x g)) κ
  simpa only [Kernel.map_apply _ (continuous_rightAction g).measurable] using h

lemma all_root_mem_iff_rational_root_mem {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ) ↔
      ∀ q : ℚ, Matrix.SpecialLinearGroup.transvection hij (q : ℝ) ∈
        invariantRightSubgroup μ := by
  constructor
  · exact fun h q => h q
  · intro h t
    exact Rat.denseRange_cast.induction_on t
      ((isClosed_invariantRightSubgroup μ).preimage (continuous_rootTransvection hij)) h

/-- Full real-root invariance is a measurable event, without replacing
the real root by a discrete-time action. -/
lemma measurableSet_kernel_root_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (κ : Kernel Z (X n)) [IsFiniteKernel κ] :
    MeasurableSet {z | ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)} := by
  have he : {z | ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)} =
      ⋂ q : ℚ, {z | Matrix.SpecialLinearGroup.transvection hij (q : ℝ) ∈
        invariantRightSubgroup (κ z)} := by
    ext z
    simp only [mem_iInter, Set.mem_ofPred_eq]
    exact all_root_mem_iff_rational_root_mem hij (κ z)
  rw [he]
  exact MeasurableSet.iInter fun q =>
    measurableSet_kernel_translation_invariant κ _

end DukePrimeDegree

end

end OAI
