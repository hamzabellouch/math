import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryVolumeAveraging

namespace OAI

/-! # Transversal estimates from the actual boundary comparison and leaf bound -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)
  (C : RayBoundaryComparison RS RT height f)

/-- The normality identity changes the right-leaf estimate into the left
translations used for Haar averaging. All boundary metric and polynomial
volume assumptions are supplied by the existing published inputs. -/
theorem RayBoundaryComparison.transversal_trace_of_leaf_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (dynkinS : NilpotentDynkinExpansionInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    {L : ℝ}
    (hleaf : ∀ p x (n : F.N.carrier),
      ‖(height (f p (x * F.inclusionN n))).toAdd - (height (f p x)).toAdd‖ ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p d d₀,
      |(C.targetRate * αT (height (f p (F.inclusionD d))).toAdd -
          C.targetRate * αT (height (f p (F.inclusionD d₀))).toAdd) -
        (C.sourceRate * αS (height (F.inclusionD d)).toAdd -
          C.sourceRate * αS (height (F.inclusionD d₀)).toAdd)| ≤ B := by
  let : IsTopologicalGroup RT.cone.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, RT.cone.Q.modelSpace)) ⊤
  let : LocallyCompactSpace RT.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RT.cone.Q.modelSpace))
  let : SecondCountableTopology
      (GroupLieAlgebra (𝓘(ℝ, RT.cone.Q.modelSpace)) RT.cone.Q.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology
      (GroupLieAlgebra (𝓘(ℝ, RS.cone.Q.modelSpace)) RS.cone.Q.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology RT.cone.Q.carrier :=
    RT.cone.maps.chartQ.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology RS.cone.Q.carrier :=
    RS.cone.maps.chartQ.symm.isEmbedding.secondCountableTopology
  let : C.targetMeasure.IsHaarMeasure := C.targetHaar
  have hscalar (p : P) (n : F.N.carrier) (d : F.D.carrier) :
      |C.targetRate * αT (height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
        C.targetRate * αT (height (f p (F.inclusionD d))).toAdd| ≤
        C.targetRate * ‖αT‖ * L := by
    have hswap : F.inclusionD d * F.inclusionN (F.action d⁻¹ n) =
        F.inclusionN n * F.inclusionD d := by
      rw [F.conjugation, map_inv, inv_inv]
      group
    have hh := hleaf p (F.inclusionD d) (F.action d⁻¹ n)
    rw [hswap] at hh
    rw [← mul_sub, ← map_sub, abs_mul, abs_of_pos C.targetRate_pos]
    change C.targetRate * ‖αT ((height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
      (height (f p (F.inclusionD d))).toAdd)‖ ≤ _
    calc
      _ ≤ C.targetRate * (‖αT‖ * ‖(height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
          (height (f p (F.inclusionD d))).toAdd‖) :=
        mul_le_mul_of_nonneg_left (αT.le_opNorm _) C.targetRate_pos.le
      _ ≤ C.targetRate * (‖αT‖ * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (norm_nonneg _)) C.targetRate_pos.le
      _ = _ := (mul_assoc _ _ _).symm
  have hπsurj : Function.Surjective RS.cone.maps.quotient :=
    fun q => ⟨RS.cone.maps.sectionMap q, RS.cone.maps.section_rightInverse q⟩
  have hact n x : RS.action (F.inclusionN n) x = RS.cone.maps.quotient n * x := by
    simpa only [map_one, mul_one, MulAut.one_apply] using RS.action_eq n 1 x
  exact C.averaged_trace metricInput dynkinS haarS RS.cone.maps.expQ RS.cone.maps.isExpQ
    (RS.cone.Q.tangent_nilpotent (M.coneQuotient_nilpotent _))
    (RS.continuous_action T hExpG realize hbijN hbijD dynkinN)
    F.inclusionN RS.cone.maps.quotient hπsurj hact F.inclusionD hscalar

end PolycyclicRecognition.CartanWordModel

end

end OAI
