import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryLeafComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryAveraging
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundedHeightEndgame

namespace OAI

/-! # Bounded affine height from the actual boundary comparisons -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {P : Type} [SimplyConnectedSpace G] [IsIsometricSMul G G]
  (height : G →* Multiplicative W) (f : P → G → G)
  (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (RS : ∀ i, M.RayBoundaryModel F ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : ∀ i, M.RayBoundaryModel F (((M.supportIn T hunimod eW).weight i).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (C : ∀ i, BoundaryVolumeComparison (RS i).action (RT i).action
    ((((M.supportIn T hunimod eW).weight i).toContinuousLinearMap).comp A.val.toContinuousLinearEquiv.toContinuousLinearMap)
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap height f)
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (metricInput : GeodesicMetricExistenceInput)
  (dynkinS : ∀ i, NilpotentDynkinExpansionInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)
  (haarS : ∀ i, NilpotentExponentialHaarInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)

include C hExpG realize hbijN chartD hchartD dynkinN metricInput dynkinS haarS in
omit [IsIsometricSMul G G] in
/-- Finitely many boundary characters give one common transversal bound. -/
theorem uniform_transversal_traces_of_boundary_comparisons
    {L : ℝ} (hleaf : ∀ p x (n : F.N.carrier),
      ‖(height (f p (x * F.inclusionN n))).toAdd - (height (f p x)).toAdd‖ ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p d i,
      |(C i).targetRate * (M.supportIn T hunimod eW).weight i ((height (f p (F.inclusionD d))).toAdd - (height (f p 1)).toAdd) -
        (C i).sourceRate * (M.supportIn T hunimod eW).weight i (A.val (height (F.inclusionD d)).toAdd)| ≤ B := by
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have htrace (i : Fin M.letterCount) := RayBoundaryComparison.transversal_trace_of_leaf_bound
    (eW := eW)
    (αS := (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap).comp
      A.val.toContinuousLinearEquiv.toContinuousLinearMap)
    (αT := ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
    T (RS i) (RT i) height f (C i) hExpG realize hbijN hbijD dynkinN
    metricInput (dynkinS i) (haarS i) hleaf
  choose bound hbound hb using htrace
  refine ⟨∑ i, bound i, Finset.sum_nonneg (fun i _ => hbound i), ?_⟩
  intro p d i
  have hh := hb i p d (1 : F.D.carrier)
  have hi : |(C i).targetRate * (M.supportIn T hunimod eW).weight i ((height (f p (F.inclusionD d))).toAdd -
      (height (f p 1)).toAdd) -
      (C i).sourceRate * (M.supportIn T hunimod eW).weight i (A.val (height (F.inclusionD d)).toAdd)| ≤ bound i := by
    simpa only [map_one, toAdd_one, map_zero, mul_zero, sub_zero, map_sub, mul_sub,
      LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv'] using hh
  exact hi.trans (Finset.single_le_sum (fun j _ => hbound j) (Finset.mem_univ i))

include C hExpG realize hbijN chartD hchartD dynkinN metricInput dynkinS haarS in
/-- The leaf and averaged traces now come from the constructed boundary
volume data. Only the already proved sublinear estimate is retained here. -/
theorem uniform_affine_bound_of_boundary_comparisons
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hsub : ∀ p ε, 0 < ε → ∃ B : ℝ, ∀ g,
      ‖(height (f p g)).toAdd - (height (f p 1)).toAdd - A.val (height g).toAdd‖ ≤
        ε * dist 1 g + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p g,
      ‖(height (f p g)).toAdd - ((height (f p 1)).toAdd + A.val (height g).toAdd)‖ ≤ K := by
  obtain ⟨L, hL, hleaf⟩ := M.nilpotent_leaf_bound_of_boundary_comparisons T F hunimod eW
    hExpG realize haarN dynkinN b₀ γ₀ height f A RS RT C
  obtain ⟨B, hB, htrace⟩ := M.uniform_transversal_traces_of_boundary_comparisons T F hunimod eW
    height f A RS RT C hExpG realize hbijN chartD hchartD dynkinN metricInput dynkinS haarS hleaf
  let β := fun i => (C i).targetRate • (M.supportIn T hunimod eW).weight i
  let α' := fun i => (C i).sourceRate • (((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap)
  have hsep : ∀ w, (∀ i, β i w = 0) → w = 0 := by
    intro w hw
    apply (M.supportIn T hunimod eW).separates w
    intro i
    have hi := hw i
    change (C i).targetRate * (M.supportIn T hunimod eW).weight i w = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (C i).targetRate_pos.ne'
  obtain ⟨_, K, hK, hb⟩ := F.uniform_affine_bound_of_leaf_and_averaged_traces T eW
    height hheight hbijN chartD hchartD α' β hsep
    (fun p g => (height (f p g)).toAdd) (fun _ => A.val.toLinearMap)
    hsub hL hB hleaf htrace
  exact ⟨K, hK, hb⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
