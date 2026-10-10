import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeHeightMultiplier
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction

namespace OAI

/-! # The actual boundary Haar action in ambient height coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter MeasureTheory
open scoped Pointwise BigOperators
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))


include hbijQ hπ hα hφ in
/-- The quotient Haar character is the actual ambient height character.
The nilpotent factor contributes only a Haar-preserving translation. -/
theorem exists_boundary_haar_height_multiplier
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hExpQ : IsGroupExponential ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α₀ → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay α₀ → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (g : G) (E : Set Q.carrier), μ (act g '' E) =
        ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μ E := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ := M.exists_cone_haar_height_multiplier T eW
    (positiveWeightRay α₀) (positiveWeightRay_add α₀) Q ExpQ hExpQ hbijQ haar
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ, ell, c, hμ, hout, hin, hell, ?_⟩
  intro g E
  obtain ⟨⟨u, d⟩, rfl⟩ := F.surjective g
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have hαeq : (fun q => α d q) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) := by
    funext q
    exact M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  have hset : act (F.inclusionN u * F.inclusionD d) '' E = π u • (α d '' E) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    funext q
    exact hact u d q
  have hh : (height (F.inclusionN u * F.inclusionD d)).toAdd =
      eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [map_mul, F.inclusionN_height_eq_one T eW height hheight hbijN, one_mul]
    exact F.inclusionD_height T eW height hheight hbijD d
  rw [hset, measure_smul, hh]
  have himage : α d '' E = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) '' E :=
    congrArg (fun k : Q.carrier → Q.carrier => k '' E) hαeq
  rw [himage]
  exact hvol h E

end PolycyclicRecognition.CartanWordModel

end

end OAI
