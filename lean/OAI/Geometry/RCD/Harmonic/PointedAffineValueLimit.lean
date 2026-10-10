import OAI.Geometry.RCD.Harmonic.ContinuousApproximateRepresentative
import OAI.Geometry.RCD.Coordinates.EuclideanCoordinateBound

namespace OAI

/-! # The affine harmonic limit controls the prescribed continuous maps -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pointed_affine_value_limit {n : ℕ} (μ : Measure X) [μ.IsOpenPosMeasure]
    (hQ : QuadraticCheegerEnergy μ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) 5 (ε k) (V k))
    (w : Fin n → ℕ → SobolevSpace μ hQ)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) (5*r k)))
    (hrep : ∀ i k, SobolevSpace.toLp μ hQ (w i k) =ᵐ[μ.restrict (ball (p k) (5*r k))]
      fun x => v k x i)
    (g : Fin n → Euclidean n → ℝ) (T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (haff : ∀ i z, z ∈ ball (0 : Euclidean n) 3 → g i z=g i 0+T z i)
    (hconv : ∀ i W, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hQ (w i k) x-g i (V k x)| ≤ δ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ3 : ρ < 3) :
    let c : Euclidean n := WithLp.toLp 2 (fun i => g i 0)
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x ∈ ball (p k) (ρ*r k),
      dist (v k x) (c+T (V k x)) ≤ η := by
  dsimp only
  let c : Euclidean n := WithLp.toLp 2 (fun i => g i 0)
  intro η hη
  let δ := η/(2*((n : ℝ)+1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hnδ : (n : ℝ)*δ ≤ η/2 := by
    have h1 : ((n : ℝ)+1)*δ=η/2 := by dsimp only [δ]; field_simp
    nlinarith [hδ]
  have hvalues : ∀ᶠ k in atTop, ∀ i : Fin n,
      ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)),
        |SobolevSpace.toLp μ hQ (w i k) x-g i (V k x)| ≤ δ :=
    eventually_all.mpr (fun i => hconv i ρ hρ (by linarith) δ hδ)
  filter_upwards [hvalues,hε.eventually (eventually_lt_nhds (show (0:ℝ)<(3-ρ)/2 by linarith)),
    hε.eventually (eventually_lt_nhds (half_pos hη))] with k hk hroom hsmall
  have hs : ball (p k) (ρ*r k) ⊆ ball (p k) (5*r k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (by linarith : ρ≤5) (hr k).le)
  have hAE : ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)),
      dist (v k x) (c+T (V k x)) ≤ (n : ℝ)*δ := by
    have hall := ae_all_iff.mpr hk
    have hrepall := ae_all_iff.mpr (fun i => ae_restrict_of_ae_restrict_of_subset hs (hrep i k))
    filter_upwards [hall,hrepall,ae_restrict_mem measurableSet_ball] with x hval hrepr hx
    rw [dist_eq_norm]
    apply euclidean_norm_le_card_mul
    intro i
    have hb := (abs_le.mp (pointed_radial_distance (hr k) (by norm_num : (0:ℝ)≤5)
      (hV k) ((hs hx).le))).2
    have hdx : dist x (p k)/r k < ρ := (div_lt_iff₀ (hr k)).mpr hx
    have hx3 : V k x ∈ ball (0 : Euclidean n) 3 := by
      simp only [mem_ball,dist_zero_right]
      linarith
    have hi := hval i
    rw [hrepr i,haff i _ hx3] at hi
    change |v k x i-(g i 0+T (V k x) i)| ≤ δ
    exact hi
  have hF : ∀ x ∈ ball (p k) (ρ*r k), ∀ y ∈ ball (p k) (ρ*r k),
      dist (c+T (V k x)) (c+T (V k y)) ≤ (r k)⁻¹*dist x y+ε k := by
    intro x hx y hy
    rw [dist_add_left,T.dist_map]
    have hh := (abs_le.mp ((hV k).2.1 x y (hs hx).le (hs hy).le)).2
    simp only [div_eq_inv_mul] at hh
    linarith
  intro x hx
  have hb := continuous_approximate_representative μ isOpen_ball (v k)
    (fun y => c+T (V k y)) ((hv k).mono hs) hF hAE x hx
  exact hb.trans (by linarith)

end RegularPointCoordinates

end

end OAI
