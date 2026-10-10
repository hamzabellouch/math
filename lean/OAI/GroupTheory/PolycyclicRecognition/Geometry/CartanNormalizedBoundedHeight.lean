import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSublinearBoundedHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedPairBackwardHeight

namespace OAI

/-! # Uniform bounded height over all normalized pairs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)



local notation "D" => supportIn M T hunimod eW
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))

include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- Finite template labels turn the published-input fixed-label bounds into
one bound for every normalized pair. The backward estimate is derived from
the forward estimate by the actual inverse normalization identity. -/
theorem uniform_normalized_affine_bound_of_published_inputs_and_sublinear
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : ∀ (A : templateSymmetryGroup D) i,
      M.PolarConeModelInputs F (positiveWeightRay ((((D).weight i).comp A.val.toLinearMap).comp θ)))
    (targetInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (((D).weight i).comp θ)))
    (sourceDynkin : ∀ (A : templateSymmetryGroup D) i
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
        M.coneWordIdeal (positiveWeightRay ((((D).weight i).comp A.val.toLinearMap).comp θ)))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (((D).weight i).comp θ)))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height (p.val.1 y)).toAdd - (height (p.val.1 x)).toAdd -
        (label p).val ((height (x⁻¹ * y)).toAdd)‖ ≤ ε * dist x y + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
      ‖(height (p.val.1 x)).toAdd - (label p).val (height x).toAdd‖ ≤ K := by
  classical
  let : Fintype (templateSymmetryGroup D) := Fintype.ofFinite _
  have hback := F.normalized_pair_backward_sublinear_height T eW height hheight
    chartD hchartD (fun p => (label p).val.toContinuousLinearEquiv) hKheight hLip hsub
  have hfiber (A : templateSymmetryGroup D) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ (p : {p : NormalizedPair G Λ // label p = A}) x,
        ‖(height (p.val.val.1 x)).toAdd - A.val (height x).toAdd‖ ≤ K := by
    obtain ⟨K, hK, hb⟩ := M.uniform_affine_bound_of_published_inputs_and_sublinear (ef := 0) (eg := 0)
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD A
      hExpG realize haarN haarD metricInput b₀ γ₀ hpath hKheight hLip
      (sourceInputs A) targetInputs (sourceDynkin A) targetDynkin
      (fun p : {p : NormalizedPair G Λ // label p = A} => p.val.val.1)
      (fun p => p.val.val.2)
      (fun p => p.val.val.1.continuous) (fun p => p.val.val.2.continuous)
      Λ.coe_nonneg Λ.coe_nonneg
      (fun p x y => by simpa only [add_zero] using p.val.property.1.1.dist_le_mul x y)
      (fun p x y => by simpa only [add_zero] using p.val.property.1.2.1.dist_le_mul x y)
      (fun p => p.val.property.1.2.2.2.2.1) (fun p => p.val.property.1.2.2.2.2.2)
      (by
        intro ε hε
        obtain ⟨B, hB, hb⟩ := hsub ε hε
        refine ⟨B, hB, ?_⟩
        intro p x y
        have h := hb p.val x (x * y)
        rw [show dist x (x * y) = dist 1 y by simpa only [mul_one] using dist_mul_left x (1 : G) y] at h
        simpa only [p.property, inv_mul_cancel_left, dist_mul_left, map_mul, map_inv,
          toAdd_mul, toAdd_inv, neg_add_eq_sub] using h)
      (by
        intro ε hε
        obtain ⟨B, hB, hb⟩ := hback ε hε
        refine ⟨B, hB, ?_⟩
        intro p x y
        have h := hb p.val x (x * y)
        rw [show dist x (x * y) = dist 1 y by simpa only [mul_one] using dist_mul_left x (1 : G) y] at h
        simpa only [p.property, inv_mul_cancel_left, dist_mul_left, map_mul, map_inv,
          toAdd_mul, toAdd_inv, neg_add_eq_sub, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_toContinuousLinearEquiv_symm'] using h)
    refine ⟨K, hK, fun p x => ?_⟩
    simpa only [p.val.property.2, map_one, toAdd_one, zero_add] using hb p x
  choose K hK hb using hfiber
  refine ⟨∑ A, K A, Finset.sum_nonneg (fun A _ => hK A), ?_⟩
  intro p x
  exact (hb (label p) ⟨p, rfl⟩ x).trans
    (Finset.single_le_sum (fun A _ => hK A) (Finset.mem_univ (label p)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
