import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentationHeightFactor
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InducingFromHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationTopology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The topology of the intrinsic triangular representation

The adjoint action recovers height continuously from the representation.
On the height kernel the nilpotent exponential chart and unique triangular
logarithm already recover the topology. Section coordinates combine them.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem intrinsic_triangular_representation_inducing
    {a m : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ)
    (hj : Function.Injective j) (hu : ∀ x, (j x).IsUpperTriangular)
    (ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ) (hρ : Continuous ρ)
    (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ (HeightSpace T.character)).equivFun
  obtain ⟨π, hπ, hπExp, _, _, ⟨s, hs, hs0, hsright⟩, _, P, hP⟩ :=
    exists_intrinsic_canonical_height_with_kernel T q hExp
  have hπc : Continuous π := hπ
  let sectionMap : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs⟩
  have hsection (w : Multiplicative W) : π (sectionMap w) = w := Multiplicative.ext (hsright w.toAdd)
  have hsection1 : sectionMap 1 = 1 := hs0
  obtain ⟨N, ExpN, hExpN, κ, hκ, _, hκExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπc hπExp
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2 ExpN hExpN
    (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  let chart : N.modelSpace ≃ₜ N.carrier := cN
  let S := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin m → Fin m)
  let J : N.modelSpace →ₗ[ℝ] S :=
    (j.toLinearMap.comp (T.kernelIdeal.incl.toLinearMap.comp N.equiv.symm.toLinearMap)).codRestrict
      S.toSubmodule (fun x => hu _)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply N.equiv.symm.injective
    apply Subtype.val_injective
    apply hj
    exact congrArg Subtype.val hxy
  have hzero : cN 0 = 1 := (hcN 0).trans hExpN.map_zero
  have hmatch (x : N.modelSpace) :
      ((ρ.comp κ) (cN x) : Matrix (Fin m) (Fin m) ℝ) = (NormedSpace.exp (J x) : S) := by
    rw [realTriangularAlgebra_coe_exp]
    change (ρ (κ (cN x)) : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (j (N.equiv.symm x))
    have hh : κ (cN x) = Exp (N.equiv.symm x) :=
      (congrArg κ (hcN x)).trans
        ((congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
          κ (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (hκExp (N.equiv.symm x)))
    have he' := congrArg Units.val (he (N.equiv.symm x))
    simp only [coe_algebraExpUnit] at he'
    exact (congrArg (fun g : G => (ρ g : Matrix (Fin m) (Fin m) ℝ)) hh).trans he'
  have hNind : Topology.IsInducing (ρ.comp κ) :=
    inducing_of_exponential_chart_and_local_logarithm S chart hzero J hJ
      (ρ.comp κ) (hρ.comp hκ.continuous) hmatch realTriangularAlgebra_exp_kernel
  let e := (kernelRealization π κ hκ hrange).toHomeomorph
  have hEq : (fun k : π.ker => ρ k) = (ρ.comp κ) ∘ e.symm := by
    funext k
    have hh : κ (e.symm k) = (k : G) := congrArg Subtype.val (e.apply_symm_apply k)
    exact (congrArg ρ hh).symm
  have hkind : Topology.IsInducing (fun k : π.ker => ρ k) := by
    rw [hEq]
    exact hNind.comp e.symm.isInducing
  obtain ⟨f, hf, hf1, hfactor⟩ :=
    exists_local_height_factor_of_representation T hExp j hj ρ he π P hP
  have hwhole := inducing_of_height_kernel ρ hρ π hπc sectionMap hsection hsection1
    hkind f hf hf1 hfactor
  exact Units.isOpenEmbedding_val.isInducing.comp hwhole

end PolycyclicRecognition

end

end OAI
