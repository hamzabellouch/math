import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasepointProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCanonicalProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLeftShift

namespace OAI

/-! # Exact changes of center for the actual Cartan profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.D.carrier]
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)

include hchartD

omit [IsTopologicalGroup G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I] in
/-- The group identity underlying basepoint comparison uses the actual
Cartan charts and the actual conjugation action. -/
theorem profileChart_basepoint_change
    (source target : Basis (Fin (finrank ℝ H)) ℝ H)
    (x : G) (u a : F.N.carrier) (k : F.D.carrier) (z : Fin (finrank ℝ H) → ℝ) :
    x * F.inclusionN a * F.profileChart source z =
      (x * (F.inclusionN u * F.inclusionD k)) *
        F.inclusionN (F.action k⁻¹ (u⁻¹ * a)) *
          F.profileChart target (wordChartLeftShift F.D.equiv chartD source target k z) := by
  have hp := wordChartLeftShift_point F.D.equiv chartD source target k z
  have hi := congrArg F.inclusionD hp
  simp only [exponentialCoordinates_apply, hchartD, map_mul, map_inv] at hi
  change F.profileChart target (wordChartLeftShift F.D.equiv chartD source target k z) =
    (F.inclusionD k)⁻¹ * F.profileChart source z at hi
  have hf := factor_basepoint_change F.action F.inclusionN F.inclusionD F.conjugation
    x u a k (exponentialCoordinates F.D.equiv chartD source z)
  simp only [map_mul, map_inv, exponentialCoordinates_apply, hchartD] at hf
  rw [hi]
  simpa only [profileChart, map_mul, map_inv] using hf.symm

/-- The raw normalized profiles satisfy the exact change-of-center identity;
all errors arise later from affine approximation, not from this formula. -/
theorem realScaleProfile_basepoint_change
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J)
    (x : G) (u a : F.N.carrier) (k : F.D.carrier)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (z : Fin (finrank ℝ H) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log s)
    let y := x * (F.inclusionN u * F.inclusionD k)
    r • F.realScaleProfile hD J hJ x X S β r a z =
      s • F.realScaleProfile hD J hJ y X S β s (F.action k⁻¹ (u⁻¹ * a))
        (wordChartLeftShift F.D.equiv chartD br bs k z) + (J y - J x) := by
  dsimp only
  simp only [realScaleProfile_apply, max_eq_left (Real.log_nonneg hr),
    max_eq_left (Real.log_nonneg hs)]
  apply rescaled_profile_basepoint_change J x _ (F.inclusionN a) _ _ _
    (zero_lt_one.trans_le hr) (zero_lt_one.trans_le hs) z _
  exact F.profileChart_basepoint_change chartD hchartD _ _ x u a k z

end PolycyclicRecognition.CartanFactorModel

end

end OAI
