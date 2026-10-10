import OAI.Geometry.RCD.Harmonic.HarmonicCountableCompactness
import OAI.Geometry.RCD.Metric.BallLimitGluing

namespace OAI

/-! # One harmonic value limit on the whole open Euclidean ball

The exhaustion is used only to construct the function. Convergence holds
on every strictly smaller physical ball through the original maps.
Identification of the Euclidean weak equation is a separate step.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem harmonic_open_ball_value_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hgradient : LocalHarmonicL2GradientInput hX)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : ℕ → X → Euclidean n)
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (u k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (u k)≤1) :
    ∃ (g : Euclidean n → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ContinuousOn g (ball 0 S) ∧
      (∀ ρ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 ρ)) ∧
      (∀ z, S≤‖z‖ → g z=0) ∧
      ∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (ρ*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)) x-g (v (a k) x)|<η := by
  let T : ℕ → ℝ := fun m => S*(1-1/((m+2:ℕ):ℝ))
  have hT (m : ℕ) : 0<T m := by
    apply mul_pos hS
    have hd : (1:ℝ)<((m+2:ℕ):ℝ) := by norm_cast; omega
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hd)
  have hTS (m : ℕ) : T m<S := by
    have hd : 0<1/((m+2:ℕ):ℝ) := by positivity
    dsimp only [T]
    nlinarith
  have hTlim : Tendsto T atTop (𝓝 S) := by
    have hd : Tendsto (fun m : ℕ => 1/((m+2:ℕ):ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
    simpa only [sub_zero,mul_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hd).const_mul S
  have hcofinal (ρ : ℝ) (hρ : ρ<S) : ∃ m, ρ<T m :=
    (hTlim.eventually (Ioi_mem_nhds hρ)).exists
  obtain ⟨G,L,a,ha,hG,hconv,hcompat⟩ := harmonic_countable_value_limits hX hn hmean hgradient
    hS T hT hTS p r ε hr hcurv hε hε1 hεlim v hv u hu hnorm
  obtain ⟨g,hgc,hgG,hgL,hg0⟩ := glue_lipschitz_ball_limits T hTS hcofinal G L hG hcompat
  refine ⟨g,a,ha,hgc,hgL,hg0,?_⟩
  intro ρ hρ hρS η hη
  obtain ⟨m,hm⟩ := hcofinal ρ hρS
  have hes : Tendsto (ε ∘ a) atTop (𝓝 0) := hεlim.comp ha.tendsto_atTop
  filter_upwards [hconv m η hη,
    hes.eventually (Iio_mem_nhds (show 0<(T m-ρ)/3 by linarith))] with k hk hek
  have hsub : ball (p (a k)) (ρ*r (a k)) ⊆ ball (p (a k)) (T m*r (a k)) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hm.le (hr (a k)).le)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hk,
    ae_restrict_mem measurableSet_ball] with x hx hball
  have hxρ : dist x (p (a k))<ρ*r (a k) := hball
  have hxS : dist x (p (a k))≤S*r (a k) :=
    hxρ.le.trans (mul_le_mul_of_nonneg_right hρS.le (hr (a k)).le)
  have hvx : v (a k) x∈ball (0:Euclidean n) (T m) := by
    have hab := (abs_le.mp ((hv (a k)).2.1 x (p (a k)) hxS
      (by simpa only [dist_self] using mul_nonneg hS.le (hr (a k)).le))).2
    have htri := dist_triangle (v (a k) x) (v (a k) (p (a k))) 0
    have hc := (hv (a k)).1
    have hrx : dist x (p (a k))/r (a k)<ρ := (div_lt_iff₀ (hr (a k))).mpr hxρ
    simp only [mem_ball,dist_zero_right] at *
    change ε (a k)<(T m-ρ)/3 at hek
    linarith
  rwa [hgG m hvx]

end RegularPointCoordinates

end

end OAI
