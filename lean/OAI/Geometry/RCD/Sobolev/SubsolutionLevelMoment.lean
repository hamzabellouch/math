import OAI.Geometry.RCD.Sobolev.SubsolutionSourceBound
import OAI.Geometry.RCD.Sobolev.LocalizedCutoffNorms
import OAI.Geometry.RCD.Sobolev.InhomogeneousSobolev

namespace OAI

/-! # Sobolev moments of upper-level weak subsolutions -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The extra potential is controlled by the gap from a preceding level.
This is the moment estimate used in the local Bochner iteration. -/
theorem NoncollapsedRCD.subsolution_level_cutoff_moment {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a : ℝ), 0 ≤ a →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball x R) u a →
      ∀ j k : ℝ, 0 ≤ j → j < k → ∀ (χ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L χ → HasCompactSupport χ →
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) → tsupport χ ⊆ ball x R →
      ∀ A : Set X, MeasurableSet A → tsupport χ ⊆ A →
      ∃ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball x R),
        (SobolevSpace.toLp _ _ w.val =ᵐ[hausdorff n X]
          fun y => χ y*max (SobolevSpace.toLp _ _ u y-k) 0) ∧
        IntegrableOn (fun y => |SobolevSpace.toLp _ _ w.val y|^p) (ball x R) (hausdorff n X) ∧
        (∫ y in ball x R, |SobolevSpace.toLp _ _ w.val y|^p ∂hausdorff n X)^(2/p) ≤
          C*((hausdorff n X).real (ball x R))^(2/p-1)*
            (10*R^2*(L:ℝ)^2+4*R^2*a*(k/(k-j))+1)*
              ∫ y in A, (max (SobolevSpace.toLp _ _ u y-j) 0)^2 ∂hausdorff n X := by
  obtain ⟨p,C,hp,hC,hS⟩ := hX.inhomogeneous_dirichlet_sobolev hn
  refine ⟨p,C,hp,hC,?_⟩
  intro x R hR hcurv u a ha hu j k hj hjk χ L hχ hs hb hΩ A hA hsA
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hk : 0 ≤ k := hj.trans hjk.le
  have habs (y : X) : |χ y| ≤ (1:ℝ≥0) := by rw [abs_of_nonneg (hb y).1]; exact (hb y).2
  have hχn (y : X) : 0 ≤ χ y := (hb y).1
  let η := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hs
  have hη := SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hs
  have hgrad : ∀ᵐ y ∂μ, |SobolevSpace.minimalSlope μ hX.quadratic η y| ≤ L := by
    filter_upwards [SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hX.quadratic hχ hs,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic η)] with y hle hnonneg
    rwa [abs_of_nonneg hnonneg]
  let v := u.upperPositivePart μ hX.quadratic hk
  let z := SobolevSpace.cutoffCLM μ hX.quadratic hχ hs habs hχn v
  let w : SobolevSpace.dirichlet μ hX.quadratic (ball x R) :=
    ⟨z,SobolevSpace.cutoffCLM_mem_dirichlet μ hX.quadratic hχ hs habs hχn hΩ v⟩
  let J := ∫ y in A, (max (SobolevSpace.toLp μ hX.quadratic u y-j) 0)^2 ∂μ
  let Jk := ∫ y in A, (SobolevSpace.toLp μ hX.quadratic v y)^2 ∂μ
  have hv : SobolevSpace.toLp μ hX.quadratic v =ᵐ[μ]
      fun y => max (SobolevSpace.toLp μ hX.quadratic u y-k) 0 := u.upperPositivePart_coe μ hX.quadratic hk
  have hJ : Jk ≤ J := by
    have hi : Integrable (fun y => (max (SobolevSpace.toLp μ hX.quadratic u y-j) 0)^2) μ := by
      apply (Lp.memLp (SobolevSpace.toLp μ hX.quadratic (u.upperPositivePart μ hX.quadratic hj))).integrable_sq.congr
      filter_upwards [u.upperPositivePart_coe μ hX.quadratic hj] with y hy
      rw [hy]
      rfl
    apply integral_mono_ae (Lp.memLp (SobolevSpace.toLp μ hX.quadratic v)).integrable_sq.integrableOn hi.integrableOn
    filter_upwards [ae_restrict_of_ae hv] with y hy
    rw [hy]
    apply pow_le_pow_left₀ (le_max_right _ _) _ 2
    exact max_le_max (by linarith) le_rfl
  let I := ∫ y, (SobolevSpace.toLp μ hX.quadratic v y)^2*(SobolevSpace.minimalSlope μ hX.quadratic η y)^2 ∂μ
  let S := ∫ y, (SobolevSpace.toLp μ hX.quadratic η y)^2*SobolevSpace.toLp μ hX.quadratic u y*
    SobolevSpace.toLp μ hX.quadratic v y ∂μ
  have hI : I ≤ (L:ℝ)^2*J :=
    (cutoff_gradient_weight_le_setIntegral μ hX.quadratic v η hη hgrad hA hsA).trans
      (mul_le_mul_of_nonneg_left hJ (sq_nonneg _))
  have hsource : S ≤ (k/(k-j))*J := by
    have heq : S = ∫ y, (χ y)^2*SobolevSpace.toLp μ hX.quadratic u y*
        max (SobolevSpace.toLp μ hX.quadratic u y-k) 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hη,hv] with y hy hvy
      rw [hy,hvy]
    rw [heq]
    exact cutoff_upper_level_source_le μ hX.quadratic u hj hjk hχ hb hsA
  have hcacc := hu.upper_level_caccioppoli μ hX.quadratic u η hk hχ hs habs hχn hΩ hη hgrad
  have hE : energyForm μ hX.quadratic w.val w.val ≤
      (10*(L:ℝ)^2+4*a*(k/(k-j)))*J := by
    have he := energy_cutoffCLM_le μ hX.quadratic v η hχ hs habs hχn hη hgrad
    change energyForm μ hX.quadratic w.val w.val ≤ _ at he
    change _ ≤ 2*a*S+4*I at hcacc
    have hs' := mul_le_mul_of_nonneg_left hsource ha
    nlinarith only [he,hcacc,hI,hs']
  have hN : ‖SobolevSpace.toLp μ hX.quadratic w.val‖^2 ≤ J := by
    have hh := cutoffCLM_norm_sq_le_setIntegral μ hX.quadratic v hχ hs habs hχn hA hsA
    have hh' : ‖SobolevSpace.toLp μ hX.quadratic w.val‖^2 ≤ Jk := by
      simpa only [NNReal.coe_one,one_pow,one_mul] using hh
    exact hh'.trans hJ
  obtain ⟨hi,hbound⟩ := hS x R hR hcurv w
  refine ⟨w,?_,hi,?_⟩
  · filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic hχ hs habs hχn v,hv] with y hz hvy
    exact hz.trans (by rw [hvy])
  · have henergy : R^2*energyForm μ hX.quadratic w.val w.val+‖SobolevSpace.toLp μ hX.quadratic w.val‖^2 ≤
        (10*R^2*(L:ℝ)^2+4*R^2*a*(k/(k-j))+1)*J := by
      have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg R)
      nlinarith only [hh,hN]
    calc
      _ ≤ C*(μ.real (ball x R))^(2/p-1)*
          ((10*R^2*(L:ℝ)^2+4*R^2*a*(k/(k-j))+1)*J) :=
        hbound.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
      _ = _ := by ring

end RegularPointCoordinates

end

end OAI
