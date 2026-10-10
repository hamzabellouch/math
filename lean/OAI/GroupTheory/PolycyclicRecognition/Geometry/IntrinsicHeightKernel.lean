import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentModelIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisSection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.KernelProductCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SplitKernelCoordinates

namespace OAI

/-! # The closed nilpotent height kernel without a global ambient chart

A product of exponential curves supplies a smooth height section. The inverse
function theorem identifies the integrated nilpotent model locally with the
kernel. The section retracts the ambient group onto the actual kernel, so
simple connectedness upgrades that local identification to a closed embedding.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold ContDiff Topology

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
theorem exists_closed_intrinsic_height_kernel :
    ∃ (N : NilpotentLieModel T.kernelIdeal)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
      IsGroupExponential ExpN ∧
      ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
        (∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x) ∧
        Set.range ι = (π.ker : Set G) := by
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel T.kernelIdeal T.kernelIdeal_nilpotent
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ :=
    N.exists_exponential_chart T.kernelIdeal_nilpotent
      (nilpotentPublishedInputs.haar T.kernelIdeal N)
  let j := T.kernelIdeal.incl.comp N.equiv.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp N.equiv.symm.injective
  obtain ⟨ι, hιsmooth, hιdiff, hιExp⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput T.kernelIdeal N)
      inferInstance (N.tangent_nilpotent T.kernelIdeal_nilpotent) j ExpN Exp hExpN hExp
  let d : E →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d :=
    q.surjective.comp (heightProjection_surjective T.character)
  obtain ⟨s, l, hs, hs0, hsπ, hsl, hdl⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπExp
  let jc : N.modelSpace →L[ℝ] E := j.toLinearMap.toContinuousLinearMap
  let dc : E →L[ℝ] W := d.toContinuousLinearMap
  have hjrange : LinearMap.range jc.toLinearMap = LinearMap.ker dc.toLinearMap := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change q (heightProjection T.character (j v)) = 0
      have hz : heightProjection T.character (j v) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (N.equiv.symm v).property
      rw [hz, map_zero]
    · intro hx
      have hz : heightProjection T.character x = 0 := by
        apply q.injective
        exact (show d x = 0 from hx).trans (map_zero q).symm
      have hxK : x ∈ T.kernelIdeal := (Submodule.Quotient.mk_eq_zero _).mp hz
      refine ⟨N.equiv ⟨x, hxK⟩, ?_⟩
      change j (N.equiv ⟨x, hxK⟩) = x
      exact congrArg Subtype.val (N.equiv.symm_apply_apply ⟨x, hxK⟩)
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
    have hz : heightProjection T.character (j v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (N.equiv.symm v).property
    rw [hπExp, hz, map_zero]
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

include T q hExp hπ hπExp in
/-- A period must lie in the height kernel, whose nilpotent exponential
coordinates and closed inclusion have both been constructed. -/
theorem exponential_eq_one_iff_of_intrinsic_height_kernel
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : Exp x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨N, ExpN, hExpN, ι, hι, _, hcompat, _⟩ :=
      exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
    obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
      ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
    have hx0 : heightProjection T.character x = 0 := by
      apply q.injective
      rw [← hπExp, hx, map_one, map_zero]
      rfl
    let xK : T.kernelIdeal := ⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx0⟩
    have hN : ExpN (N.equiv xK) = ExpN 0 := by
      apply hι.injective
      rw [hcompat, hExpN.map_zero, map_one]
      exact hx
    have hz : N.equiv xK = 0 := by
      apply cN.injective
      simpa only [hcN] using hN
    have hzK : xK = 0 := N.equiv.injective (hz.trans (map_zero N.equiv).symm)
    exact congrArg Subtype.val hzK
  · rintro rfl
    exact hExp.map_zero

include q hExp hπ hπExp in
/-- The exponential is injective on the entire canonical height kernel. -/
theorem exponential_injOn_intrinsic_height_kernel :
    InjOn Exp (T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
  obtain ⟨N, ExpN, hExpN, ι, hι, _, hcompat, _⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
    ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  intro x hx y hy hxy
  have he : ExpN (N.equiv ⟨x, hx⟩) = ExpN (N.equiv ⟨y, hy⟩) := by
    apply hι.injective
    rw [hcompat, hcompat]
    exact hxy
  have hn : N.equiv ⟨x, hx⟩ = N.equiv ⟨y, hy⟩ := by
    apply cN.injective
    simpa only [hcN] using he
  exact congrArg Subtype.val (N.equiv.injective hn)

include q hExp hπ hπExp in
/-- A kernel point has no other exponential preimage in the ambient algebra. -/
theorem exponential_eq_of_mem_intrinsic_height_kernel
    {x y : GroupLieAlgebra (𝓘(ℝ, E)) G} (hx : x ∈ T.kernelIdeal)
    (he : Exp x = Exp y) : x = y := by
  have hx0 : heightProjection T.character x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hy0 : heightProjection T.character y = 0 := by
    apply q.injective
    rw [← hπExp, ← he, hπExp, hx0, map_zero]
  exact exponential_injOn_intrinsic_height_kernel T q Exp hExp π hπ hπExp hx
    ((Submodule.Quotient.mk_eq_zero _).mp hy0) he

end PolycyclicRecognition

end

end OAI
