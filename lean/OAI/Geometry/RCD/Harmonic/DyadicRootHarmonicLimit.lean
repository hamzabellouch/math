import OAI.Geometry.RCD.Harmonic.CenteredHarmonicCompactness
import OAI.Geometry.RCD.Metric.RescaledRootBounds
import OAI.Geometry.RCD.Metric.DyadicPointedRigidity

namespace OAI

/-! # Entire limits of the actual dyadic root-normalized directions -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_harmonic_limit {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2)
    (p : ℕ → X) (r ε : ℕ → ℝ) (d : ℕ → ℕ)
    (hr : ∀ k, 0 < r k) (hd : Tendsto d atTop atTop)
    (hcurv : ∀ k, -1 ≤ K*(r k)^2)
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
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (u k i)) (z : Euclidean (m+1)) :
    ∃ (b : ℕ → ℕ) (f : Euclidean (m+1) → ℝ), StrictMono b ∧ Continuous f ∧
      InnerProductSpace.HarmonicOnNhd f univ ∧
      (∀ x, f x = f 0+fderiv ℝ f 0 x) ∧
      (∀ ρ : ℝ, ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall 0 ρ)) ∧
      ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
        dist x (p (b k)) ≤ W*r (b k) →
          |⟪v (b k) x-v (b k) (p (b k)),A (b k) z⟫_ℝ/r (b k)-f (V (b k) x)| < η := by
  have hpow : Tendsto (fun j : ℕ => (2 : ℝ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hex (j : ℕ) : ∃ N : ℕ, (j : ℝ)+1 < (2 : ℝ)^N/8 := by
    obtain ⟨N,hN⟩ := (hpow.eventually_gt_atTop (8*((j : ℝ)+1))).exists
    exact ⟨N,by linarith⟩
  choose N hN using hex
  let C : ℕ → ℝ := fun j => 2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^(N j))*‖z‖
  have hC (j : ℕ) : 0 ≤ C j := by dsimp only [C]; positivity
  let L : ℕ → ℝ≥0 := fun j => ⟨C j,hC j⟩
  let B : ℕ → ℝ := fun j => C j*((j : ℝ)+1)
  let U := fun k => sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k) (A k z)
  let v₀ := fun k x => ⟪v k x,A k z⟫_ℝ
  have hH (k : ℕ) : IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (U k) :=
    IsSobolevHarmonicOn.linearCombination (hausdorff (m+1) X) hX.quadratic (hu k) (A k z)
  have hU (k : ℕ) : SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (U k) =ᵐ[
      (hausdorff (m+1) X).restrict (ball (p k) ((2 : ℝ)^(d k)*r k))] v₀ k :=
    sobolevColumnMap_representative (hausdorff (m+1) X) hX.quadratic (u k) _ (v k) (hrep k) (A k z)
  have hdata : ∀ j : ℕ, ∀ᶠ k in atTop, -1 ≤ K*(r k)^2 ∧
      IsMeasuredEuclideanApproximation (hausdorff (m+1) X) (m+1) (p k) (r k)
        ((j : ℝ)+1) (ε k) (V k) ∧
      (∀ x, dist x (p k) ≤ ((j : ℝ)+1)*r k → |(v₀ k x-v₀ k (p k))/r k| ≤ B j) ∧
      (∀ x y, dist x (p k) ≤ ((j : ℝ)+1)*r k → dist y (p k) ≤ ((j : ℝ)+1)*r k →
        |(v₀ k x-v₀ k (p k))/r k-(v₀ k y-v₀ k (p k))/r k| ≤ (L j : ℝ)*(dist x y/r k)) := by
    intro j
    filter_upwards [hV j,hd.eventually (eventually_ge_atTop (N j))] with k hVk hNk
    have hs : ball (p k) ((2 : ℝ)^(N j)*r k) ⊆ ball (p k) ((2 : ℝ)^(d k)*r k) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNk) (hr k).le)
    have hb := dyadic_root_rescaled_bounds m hm hX ha hBG (u k) (v k) (p k)
      (hr k) hκ hκ1 hsmall (A k) (hA k) (N j)
      (fun i hi => hscale k i (hi.trans hNk)) (fun i hi => hframes k i (hi.trans hNk))
      ((hv k).mono hs) (fun i => ae_restrict_of_ae_restrict_of_subset hs (hrep k i))
      z (by positivity : 0 ≤ (j : ℝ)+1) (hN j)
    refine ⟨hcurv k,hVk,?_,?_⟩
    · simpa only [v₀,inner_sub_left] using hb.1
    · have hLval : (L j : ℝ) = 2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^(N j))*‖z‖ := rfl
      rw [hLval]
      simpa only [v₀,inner_sub_left] using hb.2
  obtain ⟨b,f,hb,hfc,hfh,hfL,hconv⟩ := hX.centered_harmonic_compactness hm p r ε
    (fun k => (2 : ℝ)^(d k)) V hr hε hε1 hεlim (hpow.comp hd) U v₀ hH hU L B
    (fun j => mul_nonneg (hC j) (by positivity)) hdata
  have hconv' : ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
      dist x (p (b k)) ≤ W*r (b k) →
        |⟪v (b k) x-v (b k) (p (b k)),A (b k) z⟫_ℝ/r (b k)-f (V (b k) x)| < η := by
    simpa only [v₀,inner_sub_left] using hconv
  let C₀ := 8*((m+1 : ℕ) : ℝ)*(‖z‖+1)
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hε' : Tendsto (fun k => 3*ε (b k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (hεlim.comp hb.tendsto_atTop).const_mul 3
  have hgrowth (j : ℕ) : ∀ᶠ k in atTop,
      IsPointedApproximation (p k) 0 (r k) ((2 : ℝ)^j) (3*ε k) (V k) ∧
      ∀ x, dist x (p k) ≤ (2 : ℝ)^j*r k →
        |⟪v k x-v k (p k),A k z⟫_ℝ/r k| ≤ C₀*(3 : ℝ)^j := by
    filter_upwards [hV ((2 : ℕ)^j),hd.eventually (eventually_ge_atTop (j+4))]
      with k hVk hj
    have hrad : (2 : ℝ)^j ≤ (((2 : ℕ)^j : ℕ) : ℝ)+1 := by
      push_cast
      linarith
    refine ⟨hVk.metric.restrict_radius (hr k) (by positivity) hrad (hε k),?_⟩
    have hs : ball (p k) ((2 : ℝ)^(j+4)*r k) ⊆ ball (p k) ((2 : ℝ)^(d k)*r k) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (hr k).le)
    have hroom : (2 : ℝ)^j < (2 : ℝ)^(j+4)/8 := by
      rw [pow_add]
      norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    have hbound := (dyadic_root_rescaled_bounds m hm hX ha hBG (u k) (v k) (p k)
      (hr k) hκ hκ1 hsmall (A k) (hA k) (j+4)
      (fun i hi => hscale k i (hi.trans hj)) (fun i hi => hframes k i (hi.trans hj))
      ((hv k).mono hs) (fun i => ae_restrict_of_ae_restrict_of_subset hs (hrep k i))
      z (by positivity : 0 ≤ (2 : ℝ)^j) hroom).1
    intro x hx
    apply (hbound x hx).trans
    have hgeom := dyadic_root_growth_geometric
      (a := ((m+1 : ℕ) : ℝ)*‖z‖) (by positivity) j
    have hcoef : 8*(((m+1 : ℕ) : ℝ)*‖z‖) ≤ C₀ := by
      dsimp only [C₀]
      nlinarith [Nat.cast_nonneg (α := ℝ) (m+1)]
    calc
      _ = 2*(((m+1 : ℕ) : ℝ)*‖z‖)*Real.sqrt ((2 : ℝ)^(j+4))*(2 : ℝ)^j := by ring
      _ ≤ (8*(((m+1 : ℕ) : ℝ)*‖z‖))*(3 : ℝ)^j := hgeom
      _ ≤ C₀*(3 : ℝ)^j := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have haffine := pointed_harmonic_limit_affine (by omega : 0 < m+1)
    (p∘b) (r∘b) (fun k => 3*ε (b k)) (V∘b) hε'
    (fun k x => ⟪v (b k) x-v (b k) (p (b k)),A (b k) z⟫_ℝ/r (b k)) f hfc hfh
    hC₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)
    (fun j => hb.tendsto_atTop.eventually (hgrowth j))
    (fun j => hconv' ((2 : ℝ)^j) (by positivity))
  exact ⟨b,f,hb,hfc,hfh,haffine,hfL,hconv'⟩

end RegularPointCoordinates

end

end OAI
