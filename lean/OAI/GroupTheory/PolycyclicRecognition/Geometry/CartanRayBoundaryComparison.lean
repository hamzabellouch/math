import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryVolumeComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryMass

namespace OAI

/-! # Boundary volume data constructed on the actual ray quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} {T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)

/-- Volume data for the actual source and target ray actions. -/
abbrev RayBoundaryComparison :=
  BoundaryVolumeComparison RS.action RT.action αS αT height f

variable [IsIsometricSMul G G] [ProperSpace G] [SimplyConnectedSpace G]

/-- The two actual Haar characters and the compact-shadow sandwich produce
all volume data required in the leaf and averaging steps. -/
theorem nonempty_rayBoundaryComparison_of_shadows
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (haarT : NilpotentExponentialHaarInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (jS jT : Fin M.letterCount)
    (hjS : (M.weight jS : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (hjT : (M.weight jT : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) :
    Nonempty (RayBoundaryComparison RS RT height f) := by
  obtain ⟨μS, rS, hμS, hrS, hvolS⟩ := RS.exists_positive_haar_height_multiplier
    T M F eW αS hExpG realize hbijN hbijD dynkinN haarS height hheight jS hjS
  obtain ⟨μT, rT, hμT, hrT, hvolT⟩ := RT.exists_positive_haar_height_multiplier
    T M F eW αT hExpG realize hbijN hbijD dynkinN haarT height hheight jT hjT
  let : μT.IsHaarMeasure := hμT
  obtain ⟨U, K, D, hK, hD, hmass, htrace⟩ := RS.exists_mass_and_equal_set_trace RT
    B f g hLf hLg hf hg hinv KS KT hKS hKT hB hC μT
    (fun x => rT * αT (height x).toAdd) hvolT
  exact ⟨⟨B, U, μS, μT, hμS, hμT, rS, rT, hrS, hrT,
    hvolS, hvolT, K, hK, hmass, D, hD, htrace⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
