import OAI.Geometry.RCD.Harmonic.DyadicRootGramConvergence
import OAI.Geometry.RCD.Harmonic.FirstOrderFromConvergingGrams
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # The prescribed root frame eventually satisfies every fixed splitting tolerance -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_eventual_splitting {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2)
    (p : ℕ → X) (r ε : ℕ → ℝ) (d : ℕ → ℕ)
    (hr : ∀ k, 0 < r k) (hd : Tendsto d atTop atTop)
    (hcurv : ∀ k, -1 ≤ K*(r k)^2)
    (hcurv5 : ∀ k, -1 ≤ K*(5*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (V : ℕ → X → Euclidean (m+1))
    (hV : ∀ j : ℕ, ∀ᶠ k in atTop, IsMeasuredEuclideanApproximation (hausdorff (m+1) X)
      (m+1) (p k) (r k) ((j : ℝ)+1) (ε k) (V k))
    (u : ℕ → Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (v : ℕ → X → Euclidean (m+1)) (A : ℕ → Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
    (hA : ∀ k, IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
      (ball (p k) (r k)) measurableSet_ball (A k))
    (hscale : ∀ k j, j ≤ d k → a*(3*((2 : ℝ)^j*r k)) ≤ 1)
    (hframes : ∀ k j, j ≤ d k → ∃ (S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
      (w : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) ((2 : ℝ)^j*r k) κ
        (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) S) w ∧
      IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
        (ball (p k) ((2 : ℝ)^j*r k)) measurableSet_ball S)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) ((2 : ℝ)^(d k)*r k)))
    (hrep : ∀ k i, SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (u k i) =ᵐ[
      (hausdorff (m+1) X).restrict (ball (p k) ((2 : ℝ)^(d k)*r k))] fun x => v k x i)
    (hu : ∀ k i, IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (u k i)) :
    ∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) (r k) β
        (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) (A k))
        (fun x => (A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x)) := by
  let μ := hausdorff (m+1) X
  obtain ⟨hg,hgram⟩ := dyadic_root_gram_convergence m hm hX ha hBG hκ hκ1 hsmall
    p r ε d hr hd hcurv hcurv5 hε hε1 hεlim V hV u v A hA hscale hframes hv hrep hu
  have hsub (k : ℕ) : ball (p k) (r k) ⊆ ball (p k) ((2 : ℝ)^(d k)*r k) :=
    ball_subset_ball (by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=d k),hr k])
  have hrep' (k : ℕ) (i : Fin (m+1)) :
      SobolevSpace.toLp μ hX.quadratic (transformedColumn μ hX.quadratic (u k) (A k) i) =ᵐ[
        μ.restrict (ball (p k) (r k))]
        fun x => ((A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x)) i := by
    have he := sobolevColumnMap_representative μ hX.quadratic (u k) (ball (p k) (r k)) (v k)
      (fun j => ae_restrict_of_ae_restrict_of_subset (hsub k) (hrep k j))
      (A k (EuclideanSpace.single i 1))
    filter_upwards [he] with x hx
    change SobolevSpace.toLp μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic (u k) (A k (EuclideanSpace.single i 1))) x = _
    rw [hx]
    have hh := ContinuousLinearMap.adjoint_inner_left
      (A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)) (EuclideanSpace.single i 1) (v k x)
    simpa only [real_inner_comm,EuclideanSpace.inner_single_right,starRingEnd_apply,
      star_trivial,one_mul,ContinuousLinearEquiv.coe_coe] using hh.symm
  have hv' (k : ℕ) : ContinuousOn
      (fun x => (A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x))
      (ball (p k) (r k)) :=
    (A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint.continuous.comp_continuousOn
      ((hv k).mono (hsub k))
  have hu' (k : ℕ) : ∀ i, IsSobolevHarmonicOn μ hX.quadratic (ball (p k) (r k))
      (transformedColumn μ hX.quadratic (u k) (A k) i) :=
    transformedColumn_harmonic μ hX.quadratic (u k) (A k) _
      (fun i => (hu k i).mono μ hX.quadratic (hsub k))
  obtain ⟨C,hC,hvol⟩ := hX.rescaled_ball_volume_factor hm (a:=1) (δ:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hcurv2 (k : ℕ) : -1 ≤ K*(2*r k)^2 := by
    by_cases hK : 0 ≤ K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · exact (hcurv5 k).trans (mul_le_mul_of_nonpos_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (hr k).le) (by linarith [hr k]) 2)
        (le_of_not_ge hK))
  apply hX.first_order_of_converging_grams p r hr
    (fun k => transformedColumn μ hX.quadratic (u k) (A k))
    (fun k x => (A k : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x))
    hrep' hv' hu' hC _ hg hgram
  intro k
  have hh := hvol (p k) (2*r k) (mul_pos (by norm_num) (hr k)) (hcurv2 k) (p k)
    (by simpa only [dist_self] using (mul_pos (by norm_num : (0:ℝ)<2) (hr k)).le)
  simpa only [show (1/2 : ℝ)*(2*r k)=r k by ring] using hh

end RegularPointCoordinates

end

end OAI
