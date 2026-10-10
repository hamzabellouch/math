import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryHaarAction

namespace OAI

/-! # Positive Haar characters on the concrete boundary rays -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (αW : W →L[ℝ] ℝ)
  (R : M.RayBoundaryModel F (αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))

/-- A retained generator makes the Haar character strictly positive on
the selected ray. No volume or trace comparison is assumed. -/
theorem RayBoundaryModel.exists_positive_haar_height_multiplier
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarQ : NilpotentExponentialHaarInput R.cone.Q.modelSpace R.cone.Q.carrier)
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (j : Fin M.letterCount)
    (hj : (M.weight j : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αW.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
    ∃ (μ : Measure R.cone.Q.carrier) (rate : ℝ), μ.IsHaarMeasure ∧ 0 < rate ∧
      ∀ g E, μ (R.action g '' E) =
        ENNReal.ofReal (Real.exp (rate * αW (height g).toAdd)) * μ E := by
  let α₀ := αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  have hbijQ : Function.Bijective R.cone.maps.expQ := by
    rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from funext R.cone.maps.chartQ_eq]
    exact R.cone.maps.chartQ.bijective
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ :=
    M.exists_boundary_haar_height_multiplier T F α₀ R.cone.Q R.cone.maps.expQ
      hbijQ hbijN hbijD dynkinN
      R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
      (fun d => cartan_action_eq_adjoint_of_published_realization
        T M F hExpG realize hbijN hbijD dynkinN d)
      eW height hheight R.cone.maps.isExpQ haarQ R.action R.action_eq
  obtain ⟨rate, hrate, he⟩ := positive_sum_on_weightRay α₀
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ)) c hout j hj (hin j hj)
  have hell' : ell = rate • αW.toLinearMap := by
    rw [hell]
    ext w
    have h := LinearMap.congr_fun he (cartanHeightSection T H (eW.symm w))
    have hp : eW (heightProjection T.character
        (H.subtype (cartanHeightSection T H (eW.symm w)))) = w := by
      change eW (heightProjection T.character
        ((cartanHeightSection T H (eW.symm w) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
      rw [cartanHeightSection_height, eW.apply_symm_apply]
    simpa only [α₀, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, cartanHeightWeight, LinearEquiv.coe_coe, hp] using h
  refine ⟨μ, rate, hμ, hrate, ?_⟩
  intro g E
  rw [hvol, hell']
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
