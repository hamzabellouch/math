import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicHeightKernel

namespace OAI

/-! # Closed integration of ideals inside the canonical height kernel -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))

include q hExp hπ hπExp in
theorem exists_closed_integration_in_height_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : I ≤ T.kernelIdeal)
    (hnil : LieRing.IsNilpotent I) (N : NilpotentLieModel I)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN) :
    ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
      ∀ x : I, ι (ExpN (N.equiv x)) = Exp x := by
  obtain ⟨K, ExpK, hExpK, κ, hκ, hκsmooth, heκ, _⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2
    ExpK hExpK (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar I N).2
    ExpN hExpN (N.tangent_nilpotent hnil)).1
  let j := K.equiv.toLieHom.comp ((LieIdeal.inclusion hI).comp N.equiv.symm.toLieHom)
  have hj : Function.Injective j := K.equiv.injective.comp
    ((LieIdeal.inclusion_injective hI).comp N.equiv.symm.injective)
  obtain ⟨f, hf, hfsmooth, _, hef, _⟩ := exists_closed_integration
    (nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput (E := K.modelSpace) (G := K.carrier) I N))
    (N.tangent_nilpotent hnil) j hj ExpN ExpK hExpN hExpK cN hcN cK hcK
  refine ⟨κ.comp f, hκ.comp hf, hκsmooth.comp hfsmooth, ?_⟩
  intro x
  change κ (f (ExpN (N.equiv x))) = Exp x
  rw [hef]
  change κ (ExpK (K.equiv ((LieIdeal.inclusion hI) (N.equiv.symm (N.equiv x))))) = Exp x
  rw [N.equiv.symm_apply_apply, heκ]
  rfl

end PolycyclicRecognition

end

end OAI
