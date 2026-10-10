import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTransformedPolarTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IndependentWeightCone

namespace OAI

/-! # Removing the polar cone vertex without changing the mixed ideal

The polar template uses a closed cone containing zero. The cone quotient
must kill the zero generalized weight space to descend the overlapping
Cartan factors. Salience and the nonzero generator weights supply this
bridge for the same mixed ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem closedWeightRay_salient {α : V} (hα : α ≠ 0) :
    (closedWeightRay α hα : ConvexCone ℝ V).Salient := by
  intro x hx hx0 hneg
  have hp : x ∈ positiveWeightRay α := by
    have hh : x ∈ (closedWeightRay α hα : Set V) := hx
    rw [closedWeightRay_eq_insert] at hh
    exact hh.resolve_left hx0
  have hn : -x ∈ positiveWeightRay α := by
    have hh : -x ∈ (closedWeightRay α hα : Set V) := hneg
    rw [closedWeightRay_eq_insert] at hh
    exact hh.resolve_left (neg_ne_zero.mpr hx0)
  exact zero_not_mem_positiveWeightRay hα (by
    simpa using positiveWeightRay_add α x hp (-x) hn)

theorem closedTwoWeightCone_salient (α η : V) (h : LinearIndependent ℝ ![α, η]) :
    (closedTwoWeightCone α η h : ConvexCone ℝ V).Salient := by
  intro x hx hx0 hneg
  have hp : x ∈ positiveWeightCone α η := by
    have hh : x ∈ (closedTwoWeightCone α η h : Set V) := hx
    rw [closedTwoWeightCone_eq_insert] at hh
    exact hh.resolve_left hx0
  have hn : -x ∈ positiveWeightCone α η := by
    have hh : -x ∈ (closedTwoWeightCone α η h : Set V) := hneg
    rw [closedTwoWeightCone_eq_insert] at hh
    exact hh.resolve_left (neg_ne_zero.mpr hx0)
  exact zero_not_mem_positiveWeightCone h (by
    simpa using positiveWeightCone_add α η x hp (-x) hn)

theorem transformedPolarCone_salient [FiniteDimensional ℝ V]
    (K : ProperCone ℝ (StrongDual ℝ V)) (A : V ≃ₗ[ℝ] V)
    (hK : (K : ConvexCone ℝ (StrongDual ℝ V)).Salient) :
    (transformedPolarCone K A : ConvexCone ℝ (StrongDual ℝ V)).Salient := by
  intro β hβ hne hneg
  have hcomp : β.comp A.toLinearMap.toContinuousLinearMap ≠ 0 := by
    intro hz
    apply hne
    ext x
    have hx := congrArg (fun f : StrongDual ℝ V => f (A.symm x)) hz
    simpa using hx
  apply hK _ hβ hcomp
  change -(β.comp A.toLinearMap.toContinuousLinearMap) ∈ K
  change (-β).comp A.toLinearMap.toContinuousLinearMap ∈ K at hneg
  simpa only [ContinuousLinearMap.neg_comp] using hneg

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem coneWordIdeal_eq_of_generator_membership
    (C D : Set (H →ₗ[ℝ] ℝ))
    (he : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C ↔ (M.weight i : H →ₗ[ℝ] ℝ) ∈ D) :
    M.coneWordIdeal C = M.coneWordIdeal D := by
  have hp : (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) =
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ D) := funext fun i => propext (not_congr (he i))
  simp only [coneWordIdeal, hp]

/-- Pullback cone with its zero height functional removed. -/
def positiveHeightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) : Set (H →ₗ[ℝ] ℝ) :=
  {χ | let f := ((χ.comp (cartanHeightSection T H)).comp
      eW.symm.toLinearMap).toContinuousLinearMap
    f ∈ K ∧ f ≠ 0}

theorem heightConePreimage_add (K : ProperCone ℝ (StrongDual ℝ W))
    {χ ψ : H →ₗ[ℝ] ℝ} (hχ : χ ∈ heightConePreimage T eW K)
    (hψ : ψ ∈ heightConePreimage T eW K) : χ + ψ ∈ heightConePreimage T eW K := by
  change ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap +
    ((ψ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap ∈ K
  exact K.add_mem hχ hψ

theorem positiveHeightConePreimage_add (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    {χ ψ : H →ₗ[ℝ] ℝ} (hχ : χ ∈ positiveHeightConePreimage T eW K)
    (hψ : ψ ∈ positiveHeightConePreimage T eW K) :
    χ + ψ ∈ positiveHeightConePreimage T eW K := by
  let f := ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap
  let g := ((ψ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap
  change f + g ∈ K ∧ f + g ≠ 0
  refine ⟨K.add_mem hχ.1 hψ.1, ?_⟩
  intro he
  have hg : g = -f := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using he)
  exact hK f hχ.1 hχ.2 (hg ▸ hψ.1)

theorem zero_not_mem_positiveHeightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) :
    (0 : H →ₗ[ℝ] ℝ) ∉ positiveHeightConePreimage T eW K := by
  simp [positiveHeightConePreimage]

include hunimod in
/-- Removing the vertex does not remove any of the nonzero generator weights. -/
theorem coneWordIdeal_positiveHeight_eq (K : ProperCone ℝ (StrongDual ℝ W)) :
    M.coneWordIdeal (positiveHeightConePreimage T eW K) =
      M.coneWordIdeal (heightConePreimage T eW K) := by
  apply M.coneWordIdeal_eq_of_generator_membership
  intro i
  change (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K ∧
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ≠ 0) ↔
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K
  exact ⟨And.left, fun h => ⟨h, M.sampling_weight_ne_zero T hunimod eW i⟩⟩

include hunimod in
/-- The closed polar cone gives the same zero-weight-killing ideal needed
to descend the action from the overlapping actual Cartan factors. -/
theorem zero_genWeightSpace_le_polarConeIdeal (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient) :
    (genWeightSpace (cartanRootIdeal H) (0 : H → ℝ)).toSubmodule ≤
      (M.coneWordIdeal (heightConePreimage T eW K)).toSubmodule := by
  rw [← M.coneWordIdeal_positiveHeight_eq T hunimod eW K]
  exact M.zero_genWeightSpace_le_coneWordIdeal (positiveHeightConePreimage T eW K)
    (fun _ hχ _ hψ => positiveHeightConePreimage_add T eW K hK hχ hψ)
    (zero_not_mem_positiveHeightConePreimage T eW K)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
