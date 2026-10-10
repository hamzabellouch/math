import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeHeightMultiplier
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction

namespace OAI

/-! # The actual cone Haar action for the offset trace tests -/

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

variable (C : Set (H →ₗ[ℝ] ℝ))
  (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection C x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))


include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_cone_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T C hadd
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective C w
  have hq : ExpQ (Q.equiv (M.coneProjection C x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection C x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection C
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T C
        hadd h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T C
            hadd h) (M.coneProjection C x)).symm


include hbijQ hπ hα hφ hadd in
/-- The quotient Haar character is the actual ambient height character.
The nilpotent factor contributes only a Haar-preserving translation. -/
theorem exists_cone_action_haar_height_multiplier
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hExpQ : IsGroupExponential ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (g : G) (E : Set Q.carrier), μ (act g '' E) =
        ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μ E := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ := M.exists_cone_haar_height_multiplier T eW
    C hadd Q ExpQ hExpQ hbijQ haar
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ, ell, c, hμ, hout, hin, hell, ?_⟩
  intro g E
  obtain ⟨⟨u, d⟩, rfl⟩ := F.surjective g
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have hαeq : (fun q => α d q) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T C hadd h) := by
    funext q
    exact M.factor_cone_quotient_action_eq_exponential T F C hadd Q ExpQ hbijQ
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
      (M.coneAdjointAutomorphism T C hadd h) '' E :=
    congrArg (fun k : Q.carrier → Q.carrier => k '' E) hαeq
  rw [himage]
  exact hvol h E

end PolycyclicRecognition.CartanWordModel

end

end OAI
