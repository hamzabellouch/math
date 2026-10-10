import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHomLinear
import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryVolumeAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents

namespace OAI

/-! # Invertible factorization of a Cartan mean after volume comparison -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))

include hπExp in
/-- Segment domination, root-factor vanishing, and actual Cartan polynomial
coordinates give an invertible factor on every point of the ambient group. -/
theorem exists_height_factor_of_cartan_domination
    (hbijN : Function.Bijective F.ExpN)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    (hroot : ∀ n, l (F.inclusionN n) = 1)
    (hdom : ∀ v : H,
      (M.supportIn T hunimod eW).segmentSupport (π (Exp v)).toAdd ≤
        (M.supportIn T hunimod eW).segmentSupport (l (Exp v)).toAdd) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ g, (l g).toAdd = A (π g).toAdd := by
  obtain ⟨lH, hlH⟩ := F.exists_linearMap_on_cartan chartD hchartD dynkinD l hl
  let q : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  have hq : Function.Surjective q := eW.surjective.comp (cartan_height_surjective T H)
  have hdom' (v : H) : (M.supportIn T hunimod eW).segmentSupport (q v) ≤
      (M.supportIn T hunimod eW).segmentSupport (lH v) := by
    change (M.supportIn T hunimod eW).segmentSupport
      (eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ _
    rw [hlH]
    simpa only [hπExp] using hdom v
  obtain ⟨A, hA⟩ := exists_linearEquiv_factor_of_support_domination
    (M.supportIn T hunimod eW) q lH hq hdom'
  refine ⟨A, ?_⟩
  intro g
  obtain ⟨⟨n, d⟩, rfl⟩ := F.surjective g
  rw [map_mul, hroot, one_mul, map_mul,
    F.inclusionN_height_eq_one T eW π hπExp hbijN, one_mul]
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨v, rfl⟩ := (hbijD.comp F.D.equiv.bijective).surjective d
  change (l (F.inclusionD (F.ExpD (F.D.equiv v)))).toAdd =
    A (π (F.inclusionD (F.ExpD (F.D.equiv v)))).toAdd
  rw [F.compatibleD, ← hlH, hA, hπExp]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
