import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseChartBounds
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasJetProfiles

namespace OAI

/-! Numerical profiles for full quadratic targets, derived before varying maps and scales. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_target_profiles {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : A.centers → Fin 3 → Fin n → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    (R a : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (ha : ∀ m, 0 ≤ a m) :
    ∃ E : A.centers → ℕ → ℝ, (∀ i m, 0 ≤ E i m) ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (Z : ι → M → Fin 4 → ℂ) (hZ : ∀ b, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z b))
        (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i b m, WeightedEstimates.WeightedBound univ s m (a m*(δ*τ)) (A.vectorPlaneRead i (Z b))) →
      ∀ i m l, WeightedEstimates.WeightedBound univ s m (E i m*δ^2)
        (A.globalPolynomialQuadraticTarget Q hQ G hG ε τ φ Z hφ hZ i l) := by
  classical
  obtain ⟨K,B,hK,hB,hjet⟩ := A.atlas_jet_profiles U hU KU hUK R hR
  choose Fp hFp hfp using fun m => A.phase_chart_gradient_bound φ hφ m
  choose Mp hMp hmp using fun m => A.phase_read_gradient_bound φ hφ m
  let Ap := fun i m => 1+a (m+tensorOrder (Q i)+1)
  have hAp (i m) : 0 < Ap i m := by dsimp [Ap]; linarith [ha (m+tensorOrder (Q i)+1)]
  choose E hE he using fun i m => A.globalPolynomialQuadraticTarget_bound Q hQ i
    (hU i) (hweight i) (hK i) m (B i (m+tensorOrder (Q i)))
    (Fp (m+tensorOrder (Q i))) (Ap i m) (Mp m)
    (hB i _) (hFp _) (hAp i m) (hMp m)
  refine ⟨E,hE,?_⟩
  intro G hG Z hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall hr hz i m l
  obtain ⟨hmap,hbound⟩ := hjet G hG s hs hs1 hr
  apply he i m G hG φ Z hφ hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 (hsmall i)
    (hmap i) (hbound i _) _ _ _ l
  · intro b
    have hh := weightedBound_comp_isometry planeCoordinateIsometry
      (A.vectorPlaneRead_smooth i (hZ b)) (hz i b (m+tensorOrder (Q i)+1))
    have heq : A.vectorPlaneRead i (Z b) ∘ planeCoordinateIsometry = A.vectorChartRead i (Z b) := by
      funext x
      simp only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    rw [heq] at hh
    apply hh.mono_const
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ.le hτ.le)
  · intro b v
    exact (hfp (m+tensorOrder (Q i)) i b s s.coe_nonneg hs1 v).restrict_open (hU i)
  · intro b v hv
    exact hmp m i b s s.coe_nonneg hs1 v hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
