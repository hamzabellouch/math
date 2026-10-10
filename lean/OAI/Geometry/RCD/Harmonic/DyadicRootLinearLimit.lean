import OAI.Geometry.RCD.Harmonic.DyadicRootHarmonicLimit
import OAI.Geometry.RCD.Harmonic.DyadicRootDirectionData
import OAI.Geometry.RCD.Metric.PointedCenteredLimit
import OAI.Geometry.RCD.Coordinates.NormalizedHarmonicLinearLimit

namespace OAI

/-! # Unit linear limits and sharp energy convergence of actual root directions -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_unit_linear_limit {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
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
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (u k i)) (z : Euclidean (m+1)) (hz : ‖z‖ = 1) :
    ∃ (b : ℕ → ℕ) (L : Euclidean (m+1) →L[ℝ] ℝ), StrictMono b ∧ ‖L‖ = 1 ∧
      (∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
        dist x (p (b k)) ≤ W*r (b k) →
          |⟪v (b k) x-v (b k) (p (b k)),A (b k) z⟫_ℝ/r (b k)-L (V (b k) x)| < η) ∧
      (∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff (m+1) X).restrict (ball (p (b k)) (3*r (b k))),
          localGamma (hausdorff (m+1) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u (b k)) (A (b k) z))
            (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u (b k)) (A (b k) z)) x ≤ 1+β) ∧
      Tendsto (fun k => ((hausdorff (m+1) X).real (ball (p (b k)) (2*r (b k))))⁻¹*
        ∫ x in ball (p (b k)) (2*r (b k)),
          |localGamma (hausdorff (m+1) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u (b k)) (A (b k) z))
            (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u (b k)) (A (b k) z)) x-1|
          ∂hausdorff (m+1) X) atTop (𝓝 0) := by
  obtain ⟨b,f,hb,hfc,_,hfa,_,hconv⟩ := dyadic_root_harmonic_limit m hm hX ha hBG
    hκ hκ1 hsmall p r ε d hr hd hcurv hε hε1 hεlim V hV u v A hA hscale hframes hv hrep hu z
  have hf0 : f 0 = 0 := by
    apply pointed_centered_limit (by norm_num : (0:ℝ)≤1) (p∘b) (r∘b) (ε∘b) (V∘b)
      (fun k => (hr (b k)).le) (hεlim.comp hb.tendsto_atTop)
      ((hb.tendsto_atTop.eventually (hV 0)).mono (fun k hk => by simpa using hk.metric))
      (fun k x => ⟪v (b k) x-v (b k) (p (b k)),A (b k) z⟫_ℝ/r (b k))
      (fun k => by simp) f hfc.continuousAt
    exact hconv 1 (by norm_num)
  let L := fderiv ℝ f 0
  have hfL : ∀ x, f x = L x := by
    intro x
    simpa only [hf0,zero_add] using hfa x
  have hgood : ∀ᶠ k in atTop, 6 ≤ d (b k) ∧
      IsMeasuredEuclideanApproximation (hausdorff (m+1) X) (m+1)
        (p (b k)) (r (b k)) 5 (ε (b k)) (V (b k)) := by
    filter_upwards [(hd.comp hb.tendsto_atTop).eventually (eventually_ge_atTop 6),
      hb.tendsto_atTop.eventually (hV 4)] with k hk hVk
    exact ⟨hk,by convert hVk using 1; norm_num⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  let α : ℕ → ℕ := fun k => b (k+N)
  have hα : StrictMono α := hb.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hgood' (k : ℕ) := hN (k+N) (Nat.le_add_left N k)
  let μ := hausdorff (m+1) X
  choose w hw hwrep hwnorm hwmean hwe using fun k =>
    dyadic_root_direction_data m hm hX ha hBG (u (α k)) (v (α k)) (p (α k)) (hr (α k))
      (hgood' k).1 hκ hκ1 hsmall (A (α k)) (hA (α k)) (hscale (α k)) (hframes (α k))
      (hv (α k)) (hrep (α k)) (hu (α k)) z
  have hwconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p (α k)) (W*r (α k))),
        |SobolevSpace.toLp μ hX.quadratic (w k) x-L (V (α k) x)| ≤ η := by
    intro W hW hW5 η hη
    filter_upwards [(tendsto_add_atTop_nat N).eventually (hconv W hW η hη)] with k hk
    have hs : ball (p (α k)) (W*r (α k)) ⊆ ball (p (α k)) (5*r (α k)) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right hW5.le (hr (α k)).le)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (hwrep k),
      ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    have hh := hk x (show dist x (p (α k)) ≤ W*r (α k) from hball.le)
    rw [hfL] at hh
    exact hh.le
  have hM : 0 < 80*((m+1 : ℕ) : ℝ)*‖z‖ := by rw [hz]; positivity
  have hwmean' (k : ℕ) : (μ.real (ball (p (α k)) (r (α k))))⁻¹*
      (∫ x in ball (p (α k)) (r (α k)), r (α k)^2*localGamma μ hX.quadratic (w k) (w k) x ∂μ) = 1 := by
    simpa only [hz,one_pow] using hwmean k
  have hLn := hX.normalized_harmonic_linear_limit_norm hm (p∘α) (r∘α) (ε∘α) (V∘α)
    (fun k => hr (α k)) (fun k => hcurv (α k)) (fun k => hcurv5 (α k))
    (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop)
    (fun k => (hgood' k).2) w hw hM hwnorm hwmean' L hwconv
  have hs := hX.harmonic_linear_sharp hm (p∘α) (r∘α) (ε∘α) (V∘α)
    (fun k => hr (α k)) (fun k => hcurv (α k)) (fun k => hcurv5 (α k))
    (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop)
    (fun k => (hgood' k).2) w hw hM hwnorm L hLn.le hwconv
  have he := hX.harmonic_linear_energy_l1 hm (p∘α) (r∘α) (ε∘α) (V∘α)
    (fun k => hr (α k)) (fun k => hcurv (α k)) (fun k => hcurv5 (α k))
    (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop)
    (fun k => (hgood' k).2) w hw hM hwnorm L hLn hwconv
  refine ⟨α,L,hα,hLn,?_,?_,?_⟩
  · intro W hW η hη
    filter_upwards [(tendsto_add_atTop_nat N).eventually (hconv W hW η hη)] with k hk
    simpa only [hfL] using hk
  · intro β hβ
    filter_upwards [hs β hβ] with k hk
    filter_upwards [hk,ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith [hr (α k)] : 3*r (α k) ≤ 5*r (α k))) (hwe k)] with x hx heq
    change r (α k)^2*localGamma μ hX.quadratic (w k) (w k) x ≤ 1+β at hx
    rwa [heq] at hx
  · convert he using 1
    funext k
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith [hr (α k)] : 2*r (α k) ≤ 5*r (α k))) (hwe k)] with x hx
    exact congrArg (fun t : ℝ => |t-1|) hx.symm

end RegularPointCoordinates

end

end OAI
