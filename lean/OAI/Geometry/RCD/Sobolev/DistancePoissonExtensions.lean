import OAI.Geometry.RCD.Sobolev.DistancePoissonGradient
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension

namespace OAI

/-! # Actual compact extensions of the near-regular Poisson replacements -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.distance_poisson_family_extensions {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hK : K≤0) (p₀ : X) {κ B : ℝ} (hκ : 0≤κ) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ A : ℝ, 0<A ∧ ∀ (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (J C : ℝ)
      (F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J C p r hr)
      (k : ℕ), r k≤1 → -1≤K*(64*r k)^2 →
      ∃ (G : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
        (d : Lp ℝ 2 (hausdorff n X)),
        IsWeakLaplacian (hausdorff n X) hX.quadratic G.val d ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G.val
          =ᵐ[(hausdorff n X).restrict (ball (p k) (r k/16))]
            SobolevSpace.toLp (hausdorff n X) hX.quadratic (F.replacement k) ∧
        (d =ᵐ[(hausdorff n X).restrict (ball (p k) (r k/16))]
          fun _ => (n:ℝ)+κ*(4*r k)^2) ∧
        (∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (r k/16)),
          localGamma (hausdorff n X) hX.quadratic G.val G.val x≤(A*r k)^2) := by
  let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  dsimp only
  obtain ⟨A,hA,hgrad⟩ := hX.distance_poisson_family_gradient hn hK p₀ hκ
  refine ⟨A,hA,?_⟩
  intro p r hr J C F k hr1 hc
  have hk : 0<r k := hr k
  have hc' : -1≤K*(r k/16)^2 := by nlinarith only [hc]
  have hL := hgrad p r hr J C F k (p k) hr1 (by simpa only [dist_self] using
    (div_pos hk (by norm_num : (0:ℝ)<4)).le) hc'
  let L : ℝ≥0 := ⟨A*r k,mul_nonneg hA.le (hr k).le⟩
  have hf := (F.laplacian k).mono (hausdorff n X) hX.quadratic measurableSet_ball
    (ball_subset_ball (show r k/4≤r k by linarith [hr k]))
  obtain ⟨G,d,hGd,hGF,hda⟩ := hX.local_poisson_regular_extension hn
    (F.replacement k) ((n:ℝ)+κ*(4*r k)^2) (by positivity : 0<r k/16)
    (by linarith [hr k] : 2*(r k/16)<r k/4) hf L hL
  refine ⟨G,d,hGd,hGF,hda,?_⟩
  have he := localGamma_pair_congr_ae (hausdorff n X) hX.quadratic hGF hGF
  filter_upwards [he,ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (show r k/16≤r k/4 by linarith [hr k])) hL] with x hx hbound
  exact hx ▸ hbound

end RegularPointCoordinates

end

end OAI
