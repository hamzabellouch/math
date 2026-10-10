import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # The source height has the exact identity profile on every nilpotent sheet -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

theorem rescaled_height_profile_eq
    {G W Z : Type*} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (x k : G) (r : ℝ) (hk : π k = 1)
    (φ : Z → G) (q : Z → W) (hφ : ∀ z, (π (φ z)).toAdd = Real.exp r • q z) (z : Z) :
    rescaledMapProfile (fun g => (π g).toAdd) x k r φ z = q z := by
  simp only [rescaledMapProfile, map_mul, hk, mul_one, toAdd_mul, hφ,
    add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero r), one_smul]

namespace CartanFactorModel

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem source_height_profile_eq
    (π : G →* Multiplicative W)
    (hπ : ∀ y, (π (Exp y)).toAdd = eW (heightProjection T.character y))
    (hbijN : Function.Bijective F.ExpN)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r : ℝ} (hr : 0 < r) (x : G) (n : F.N.carrier)
    (z : Fin (finrank ℝ H) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (Real.log r)
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    rescaledMapProfile (fun g => (π g).toAdd) x (F.inclusionN n) (Real.log r)
      (fun w => Exp ((br.equivFun.symm w : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z =
      height (b.equivFun.symm z) := by
  dsimp only
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hkill (y w : H) : height ⁅y, w⁆ = 0 := by
    change eW (heightProjection T.character ⁅(y : GroupLieAlgebra (𝓘(ℝ, EG)) G), w⁆) = 0
    rw [T.height_lie, map_zero]
  apply rescaled_height_profile_eq π x (F.inclusionN n) (Real.log r)
    (F.inclusionN_height_eq_one T eW π hπ hbijN n)
  intro w
  rw [hπ, Real.exp_log hr]
  simpa [bracketWordExponent_one, height] using word_length_chart_height X S β height hkill hr w

end CartanFactorModel
end PolycyclicRecognition

end

end OAI
