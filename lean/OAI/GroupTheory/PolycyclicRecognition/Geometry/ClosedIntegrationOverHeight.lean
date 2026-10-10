import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClosedEmbeddingSplitKernel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # Closed nilpotent integration over the canonical height quotient

A nilpotent subalgebra projecting onto height has a closed integrated image.
The proof compares its kernel with the constructed nilpotent height kernel
and uses section coordinates for the remaining directions.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
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
theorem exists_closed_nilpotent_integration_over_height
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (j : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier →ₗ⁅ℝ⁆
      GroupLieAlgebra (𝓘(ℝ, E)) G) (hj : Function.Injective j)
    (hsurj : Function.Surjective
      ((q.toLinearMap.comp (heightProjection T.character)).comp j.toLinearMap)) :
    ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
      ∀ (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN → ∀ x, ι (ExpN x) = Exp (j x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ := N.exists_exponential_chart hnil
    (nilpotentPublishedInputs.haar L N)
  obtain ⟨ι, hι, hdι, heι⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput L N)
      inferInstance (N.tangent_nilpotent hnil) j ExpN Exp hExpN hExp
  obtain ⟨K, ExpK, hExpK, κ, hκ, _, heκ, hrκ⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  let : IsTopologicalGroup K.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, K.modelSpace)) ⊤
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2
    ExpK hExpK (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  let d := (q.toLinearMap.comp (heightProjection T.character)).comp j.toLinearMap
  have hquot (x : N.modelSpace) : (π (ι (ExpN x))).toAdd = d x := by
    exact (congrArg (fun g : G => (π g).toAdd) (heι x)).trans (hπExp (j x))
  obtain ⟨s, hs, _, hsright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExpN d hsurj
      (π.comp ι) hquot
  let sectionN : C(Multiplicative W, N.carrier) := ⟨fun w => s w.toAdd, hs⟩
  have hsN (w : Multiplicative W) : π (ι (sectionN w)) = w :=
    Multiplicative.ext (hsright w.toAdd)
  let eN : d.ker ≃ₜ (π.comp ι).ker := cN.subtype (fun x => by
    change d x = 0 ↔ π (ι (cN x)) = 1
    rw [hcN]
    constructor
    · intro hx
      apply Multiplicative.ext
      exact (hquot x).trans hx
    · intro hx
      exact (hquot x).symm.trans (congrArg Multiplicative.toAdd hx))
  let eK : K.modelSpace ≃ₜ π.ker := cK.trans (kernelRealization π κ hκ hrκ).toHomeomorph
  let jK : d.ker →ₗ[ℝ] K.modelSpace :=
    K.equiv.toLinearMap.comp
      ((j.toLinearMap.comp d.ker.subtype).codRestrict T.kernelIdeal.toSubmodule (by
        intro x
        apply (Submodule.Quotient.mk_eq_zero _).mp
        apply q.injective
        exact (show d x = 0 from x.property).trans (map_zero q).symm))
  have hjK : Function.Injective jK := by
    intro x y h
    apply Subtype.ext
    apply hj
    have hh := K.equiv.injective h
    exact congrArg Subtype.val hh
  have hclosedKernel : Topology.IsClosedEmbedding (splitKernelHom ι π) := by
    apply isClosedEmbedding_of_compatible_charts eN eK jK hjK
    intro x
    apply Subtype.ext
    change ι (cN x) = κ (cK (jK x))
    have hh := heκ (K.equiv.symm (jK x))
    have hh' : κ (ExpK (jK x)) = Exp (K.equiv.symm (jK x)).val :=
      (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, K.modelSpace)) K.carrier => κ (ExpK y))
        (K.equiv.apply_symm_apply (jK x))).symm.trans hh
    have hcancel : (K.equiv.symm (jK x)).val = j x :=
      congrArg Subtype.val (K.equiv.symm_apply_apply _)
    exact ((congrArg ι (hcN x)).trans (heι x)).trans
      (((congrArg κ (hcK (jK x))).trans hh').trans (congrArg Exp hcancel)).symm
  refine ⟨ι, closedEmbedding_of_splitKernel ι hι.continuous π hπ sectionN hsN hclosedKernel,
    hι, ?_⟩
  intro ExpN' hExpN' x
  rw [← hExpN.unique hExpN']
  exact heι x

end PolycyclicRecognition

end

end OAI
