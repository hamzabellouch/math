import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicHeightKernel

namespace OAI

/-! # Closed integration of a nilpotent linear kernel

The split-coordinate argument for the real height kernel also applies to the
complex adjoint weights, viewed as a real linear quotient. Only nilpotence,
surjectivity and the exact exponential identity are used.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold ContDiff Topology

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Integrate the nilpotent kernel of an actual surjective linear group
character as a closed subgroup of the given simply connected Lie group. -/
theorem exists_closed_nilpotent_linear_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hnil : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : ∀ x, d x = 0 ↔ x ∈ I)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ (N : NilpotentLieModel I)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
      IsGroupExponential ExpN ∧
      ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
        (∀ x : I, ι (ExpN (N.equiv x)) = Exp x) ∧
        Set.range ι = (π.ker : Set G) := by
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel I hnil
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ :=
    N.exists_exponential_chart hnil (nilpotentPublishedInputs.haar I N)
  let j := I.incl.comp N.equiv.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp N.equiv.symm.injective
  obtain ⟨ι, hιsmooth, hιdiff, hιExp⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput I N)
      inferInstance (N.tangent_nilpotent hnil) j ExpN Exp hExpN hExp
  obtain ⟨s, l, hs, hs0, hsπ, hsl, hdl⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπExp
  let jc : N.modelSpace →L[ℝ] E := j.toLinearMap.toContinuousLinearMap
  let dc : E →L[ℝ] W := d.toContinuousLinearMap
  have hjrange : LinearMap.range jc.toLinearMap = LinearMap.ker dc.toLinearMap := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (hker (j v)).mpr (N.equiv.symm v).property
    · intro hx
      have hxI : x ∈ I := (hker x).mp hx
      refine ⟨N.equiv ⟨x, hxI⟩, ?_⟩
      exact congrArg Subtype.val (N.equiv.symm_apply_apply ⟨x, hxI⟩)
  have hdcl : dc.comp l = ContinuousLinearMap.id ℝ W := by
    ext w
    exact LinearMap.congr_fun hdl w
  have hιj : HasMFDerivAt (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ι 1 jc := by
    apply (hιsmooth.mdifferentiable (by simp) 1).hasMFDerivAt.congr_mfderiv
    ext v
    exact hιdiff v
  have hcoordinates := kernel_product_local_coordinates ι s 1 hιsmooth hs
    (map_one ι) hs0 jc dc l hιj hsl hj hjrange hdcl
  have hιker (n : N.carrier) : π (ι n) = 1 := by
    obtain ⟨v, hv⟩ := cN.surjective n
    rw [hcN] at hv
    rw [← hv, hιExp]
    apply Multiplicative.ext
    change (π (Exp (j v))).toAdd = 0
    rw [hπExp]
    exact (hker (j v)).mpr (N.equiv.symm v).property
  let sectionMap : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs.continuous⟩
  have hsection (w : Multiplicative W) : π (sectionMap w) = w :=
    Multiplicative.ext (hsπ w.toAdd)
  have hsection1 : sectionMap 1 = 1 := hs0
  let : LocallyPathConnectedSpace N.carrier :=
    ChartedSpace.locallyPathConnectedSpace N.modelSpace N.carrier
  have hinj : ∃ U ∈ 𝓝 ((1 : N.carrier), (1 : Multiplicative W)),
      InjOn (fun p : N.carrier × Multiplicative W => ι p.1 * sectionMap p.2) U :=
    hcoordinates.1
  have hmap : map (fun p : N.carrier × Multiplicative W => ι p.1 * sectionMap p.2)
      (𝓝 (1, 1)) = 𝓝 (1 : G) := hcoordinates.2
  obtain ⟨hclosed, hrange⟩ := closedEmbedding_kernel_of_split_coordinates
    π hπ sectionMap hsection hsection1 ι hιker hinj hmap
  refine ⟨N, ExpN, hExpN, ι, hclosed, hιsmooth, ?_, hrange⟩
  intro x
  simpa [j] using hιExp (N.equiv x)

end PolycyclicRecognition

end

end OAI
