import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput

namespace OAI

/-! # The actual nilpotent group of the canonical height kernel -/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Manifold

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
  (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hcG : ∀ v, cG v = Exp v)

include T q Exp hπExp hcG in
omit [SimplyConnectedSpace G] in
theorem exists_continuous_height_section :
    ∃ s : C(Multiplicative W, G), ∀ w, π (s w) = w := by
  let f : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] W :=
    q.toLinearMap.comp (heightProjection T.character)
  have hf : Function.Surjective f :=
    q.surjective.comp (heightProjection_surjective T.character)
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let s : C(Multiplicative W, G) :=
    ⟨fun w => cG (σ w.toAdd), cG.continuous.comp σ.toContinuousLinearMap.continuous⟩
  refine ⟨s, fun w => ?_⟩
  apply Multiplicative.ext
  change (π (cG (σ w.toAdd))).toAdd = w.toAdd
  rw [hcG, hπExp]
  exact LinearMap.congr_fun hσ w.toAdd

include q hExp hπExp cG hcG in
omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] in
theorem exists_closed_height_kernel
    (existN : NilpotentLieExistenceInput T.kernelIdeal)
    (haarN : ∀ N : NilpotentLieModel T.kernelIdeal,
      NilpotentExponentialHaarInput N.modelSpace N.carrier)
    (integrate : ∀ N : NilpotentLieModel T.kernelIdeal,
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := E) (G := G)) :
    ∃ (N : NilpotentLieModel T.kernelIdeal)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
      IsGroupExponential ExpN ∧
      ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
        (∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x) ∧
        Set.range ι = (π.ker : Set G) := by
  obtain ⟨N⟩ := existN T.kernelIdeal_nilpotent
  obtain ⟨ExpN, hExpN, cN, hcN⟩ :=
    N.exists_exponential_chart T.kernelIdeal_nilpotent (haarN N)
  let j := T.kernelIdeal.incl.comp N.equiv.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp N.equiv.symm.injective
  obtain ⟨ι, hclosed, _hsmooth, _hdiff, hι, hrange⟩ := exists_closed_integration
    (integrate N) (N.tangent_nilpotent T.kernelIdeal_nilpotent) j hj
    ExpN Exp hExpN hExp cN hcN cG hcG
  refine ⟨N, ExpN, hExpN, ι, hclosed, ?_, ?_⟩
  · intro x
    simpa [j] using hι (N.equiv x)
  · rw [hrange]
    ext g
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      change π (Exp (j v)) = 1
      apply Multiplicative.ext
      rw [hπExp]
      have hz : heightProjection T.character (j v) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (N.equiv.symm v).property
      rw [hz, map_zero]
      rfl
    · intro hg
      obtain ⟨v, hv⟩ := cG.surjective g
      rw [hcG] at hv
      have hz : heightProjection T.character v = 0 := by
        apply q.injective
        rw [← hπExp, hv, show π g = 1 from hg, map_zero]
        rfl
      have hmem : v ∈ T.kernelIdeal := (Submodule.Quotient.mk_eq_zero _).mp hz
      refine ⟨v, ⟨N.equiv ⟨v, hmem⟩, ?_⟩, hv⟩
      simp [j]

end PolycyclicRecognition

end

end OAI
