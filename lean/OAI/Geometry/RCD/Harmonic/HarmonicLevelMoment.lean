import OAI.Geometry.RCD.Sobolev.LocalizedCutoffNorms
import OAI.Geometry.RCD.Harmonic.UpperLevelCaccioppoli
import OAI.Geometry.RCD.Sobolev.InhomogeneousSobolev

namespace OAI

/-! # A superquadratic moment for harmonic upper-level cutoff functions -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Caccioppoli and the relative Sobolev estimate give a moment bound for
the actual cutoff of each harmonic upper-level part. -/
theorem NoncollapsedRCD.harmonic_level_cutoff_moment {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball x R) u →
      ∀ k : ℝ, 0 ≤ k → ∀ (χ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L χ → HasCompactSupport χ →
      (∀ y, |χ y| ≤ (1:ℝ≥0)) → (∀ y, 0 ≤ χ y) →
      tsupport χ ⊆ ball x R → ∀ A : Set X, MeasurableSet A → tsupport χ ⊆ A →
      ∃ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball x R),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val =ᵐ[hausdorff n X]
          fun y => χ y*max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-k) 0) ∧
        IntegrableOn (fun y => |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p)
          (ball x R) (hausdorff n X) ∧
        (∫ y in ball x R, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p
          ∂hausdorff n X)^(2/p) ≤
        C*((hausdorff n X).real (ball x R))^(2/p-1)*(10*R^2*(L:ℝ)^2+1)*
          ∫ y in A, (max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-k) 0)^2
            ∂hausdorff n X := by
  obtain ⟨p,C,hp,hC,hS⟩ := hX.inhomogeneous_dirichlet_sobolev hn
  refine ⟨p,C,hp,hC,?_⟩
  intro x R hR hcurv u hu k hk χ L hχ hs hb hχn hΩ A hA hsA
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let η := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hs
  have hη := SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hs
  have hgrad : ∀ᵐ y ∂μ, |SobolevSpace.minimalSlope μ hX.quadratic η y| ≤ L := by
    filter_upwards [SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hX.quadratic hχ hs,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic η)] with y hle hnonneg
    rwa [abs_of_nonneg hnonneg]
  let v := u.upperPositivePart μ hX.quadratic hk
  let z := SobolevSpace.cutoffCLM μ hX.quadratic hχ hs hb hχn v
  let w : SobolevSpace.dirichlet μ hX.quadratic (ball x R) :=
    ⟨z,SobolevSpace.cutoffCLM_mem_dirichlet μ hX.quadratic hχ hs hb hχn hΩ v⟩
  let J := ∫ y in A, (SobolevSpace.toLp μ hX.quadratic v y)^2 ∂μ
  let I := ∫ y, (SobolevSpace.toLp μ hX.quadratic v y)^2*
    (SobolevSpace.minimalSlope μ hX.quadratic η y)^2 ∂μ
  have hcacc : (∫ y, (SobolevSpace.toLp μ hX.quadratic η y)^2*
      (SobolevSpace.minimalSlope μ hX.quadratic v y)^2 ∂μ) ≤ 4*I :=
    hu.upper_level_caccioppoli μ hX.quadratic u η hk hχ hs hb hχn hΩ hη hgrad
  have hI : I ≤ (L:ℝ)^2*J :=
    cutoff_gradient_weight_le_setIntegral μ hX.quadratic v η hη hgrad hA hsA
  have hE : energyForm μ hX.quadratic w.val w.val ≤ 10*(L:ℝ)^2*J := by
    have he := energy_cutoffCLM_le μ hX.quadratic v η hχ hs hb hχn hη hgrad
    change energyForm μ hX.quadratic w.val w.val ≤ _ at he
    nlinarith only [he,hcacc,hI]
  have hN : ‖SobolevSpace.toLp μ hX.quadratic w.val‖^2 ≤ J := by
    simpa only [NNReal.coe_one,one_pow,one_mul] using
      cutoffCLM_norm_sq_le_setIntegral μ hX.quadratic v hχ hs hb hχn hA hsA
  obtain ⟨hi,hbound⟩ := hS x R hR hcurv w
  have hv : SobolevSpace.toLp μ hX.quadratic v =ᵐ[μ]
      fun y => max (SobolevSpace.toLp μ hX.quadratic u y-k) 0 :=
    u.upperPositivePart_coe μ hX.quadratic hk
  have hJ : J = ∫ y in A, (max (SobolevSpace.toLp μ hX.quadratic u y-k) 0)^2 ∂μ :=
    integral_congr_ae ((ae_restrict_of_ae hv).mono fun y hy => congrArg (fun t : ℝ => t^2) hy)
  refine ⟨w,?_,hi,?_⟩
  · filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic hχ hs hb hχn v,hv] with y hz hvy
    exact hz.trans (by rw [hvy])
  · have henergy : R^2*energyForm μ hX.quadratic w.val w.val+
        ‖SobolevSpace.toLp μ hX.quadratic w.val‖^2 ≤ (10*R^2*(L:ℝ)^2+1)*J := by
      have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg R)
      nlinarith only [hh,hN]
    calc
      _ ≤ C*(μ.real (ball x R))^(2/p-1)*((10*R^2*(L:ℝ)^2+1)*J) :=
        hbound.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
      _ = _ := by rw [hJ]; ring

end RegularPointCoordinates

end

end OAI
