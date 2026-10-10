import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAmbientAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeHaarAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntegratedAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredCone
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # Polar quotient actions from the precise published realization -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Matrix.Norms.Operator

/-- The published faithful exponential realization constructs the actual
polar quotient action and its Haar multiplier for the already constructed
cone model. It contributes no metric or chosen-height compatibility. -/
theorem MeasuredCone.polar_action_haar_of_published_realization
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (D : M.MeasuredCone F (heightConePreimage T eW K))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v)) :
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ d n, α d (D.maps.quotient n) = D.maps.quotient (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉ K → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K → 0 < c i) ∧
      ∀ g E, μ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μ E := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  have hN (x : cartanRootIdeal H) :
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x) := by
    rw [F.compatibleN, hmatch]
  have hD (h : H) :
      ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h) := by
    rw [F.compatibleD, hmatch]
  have hbijQ : Function.Bijective D.maps.expQ :=
    funext D.maps.chartQ_eq ▸ D.maps.chartQ.bijective
  exact M.exists_polar_cone_action_haar F T hunimod eW j ρ hρ hN hD hNbij hDbij
    dynkin K hK D.Q D.maps.expQ D.maps.isExpQ hbijQ haarQ D.maps.quotient
    D.maps.sectionMap D.maps.section_rightInverse D.maps.kernel_eq D.maps.quotient_exp
    height hheight

end PolycyclicRecognition.CartanWordModel

end

end OAI
