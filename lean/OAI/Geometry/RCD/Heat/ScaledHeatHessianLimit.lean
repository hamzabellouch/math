import OAI.Geometry.RCD.Heat.HeatCanonicalHessianControl
import OAI.Geometry.RCD.Heat.HeatBochnerIdentitySource
import OAI.Geometry.RCD.Sobolev.ScaledHessianYoungLimit

namespace OAI

/-! # Vanishing scaled canonical Hessians of the actual heat family -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem scaled_heat_hessian_limit (hK : K ≤ 0)
    (p : ℕ → X) (r s : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hs : ∀ k, 0 < s k)
    (f : ℕ → Lp ℝ 2 (hausdorff n X)) (A : ℕ → ℝ≥0)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |f k x| ≤ A k)
    (G : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)]
    (v : ℕ → Y → SobolevSpace (hausdorff n X) hX.quadratic)
    (V : ℕ → Y → X → ℝ) (Lv : ℕ → ℝ≥0) (Av : ℕ → Y → ℝ≥0)
    (hV : ∀ k y, LipschitzWith (Lv k) (V k y))
    (hVc : ∀ k y, HasCompactSupport (V k y))
    (hv : ∀ k y, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k y) =ᵐ[hausdorff n X] V k y)
    (hAv : ∀ k y, ∀ᵐ x ∂hausdorff n X,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k y) x| ≤ Av k y)
    {L : ℝ} (_hL : 0 ≤ L) (hLv : ∀ k, (Lv k:ℝ) ≤ L*r k)
    (φ : ℕ → X → ℝ) (hφ : ∀ k, AEStronglyMeasurable (φ k) (hausdorff n X))
    (hφb : ∀ k, ∀ᵐ x ∂hausdorff n X, |φ k x| ≤ (1:ℝ≥0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w k := heatSobolev m q (s k) (hs k) (f k)
    let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
      (-heatGeneratorAt m q (s k-s k/2) (f k))
    (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) →
    (∀ k (ψ : SobolevSpace m q) (b : X → ℝ), Continuous b → HasCompactSupport b →
      tsupport b ⊆ ball (p k) (2*r k) → SobolevSpace.toLp m q ψ =ᵐ[m] b →
      (∫ x, b x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
        weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
        K*weightedGamma m q b (w k) (w k)) →
    Tendsto (fun k => (r k)^2*(σ k).real (closedBall (p k) (r k))/
      m.real (ball (p k) (8*r k))) atTop (𝓝 0) →
    ∀ (J : ∀ k, Y → Lp ℝ 1 (m.restrict (closedBall (p k) (r k)))),
      (∀ k y, IsCanonicalHeatHessian m q (w k) (v k y) (p k) (r k) (φ k) (J k y)) →
      TendstoUniformly (fun k y => (∫ x in closedBall (p k) (r k), |J k y x| ∂m)/
        (r k*m.real (ball (p k) (8*r k)))) (fun _ => 0) atTop := by
  intro m q w D hG hσ hmass J hJ
  have hm (k : ℕ) : 0 < m.real (ball (p k) (8*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by linarith [hr k])).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  apply scaled_hessian_young_limit r (fun k => m.real (ball (p k) (8*r k)))
    (fun k => (σ k).real (closedBall (p k) (r k)))
    (fun k y => ∫ x in closedBall (p k) (r k), |J k y x| ∂m)
    hr hm (C := (L*Real.exp |K|)^4) (by positivity)
    (fun k y => integral_nonneg fun x => abs_nonneg _) hmass
  intro k y a ha
  have hsrc := bochner_laplacian_of_energy_identity m q K (w k) (D k) (G k) (hG k) (σ k) (hσ k)
  have hb := hX.heat_canonical_hessian_young hn (p k) hK (f k) (A k) (hA k)
    (hs k) (hr k) (G k) (σ k) (hG k) hsrc (v k y) (V k y) (Lv k) (Av k y)
    (hV k y) (hVc k y) (hv k y) (hAv k y) (φ k) (hφ k) 1 (hφb k) (J k y) (hJ k y) ha
  have hvol : m.real (closedBall (p k) (r k)) ≤ m.real (ball (p k) (8*r k)) :=
    measureReal_mono (closedBall_subset_ball (by linarith [hr k]))
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hcoef : ((1:ℝ)*((Lv k:ℝ)*Real.exp |K|)^2)^2 ≤
      (L*Real.exp |K|)^4*(r k)^4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg (Lv k).coe_nonneg (Real.exp_pos |K|).le)
      (mul_le_mul_of_nonneg_right (hLv k) (Real.exp_pos |K|).le) 4
    convert hh using 1 <;> ring
  calc
    _ ≤ 4*a^2*m.real (closedBall (p k) (r k))+
        ((1:ℝ)*((Lv k:ℝ)*Real.exp |K|)^2)^2*(σ k).real (closedBall (p k) (r k)) := hb
    _ ≤ 4*a^2*m.real (ball (p k) (8*r k))+
        ((L*Real.exp |K|)^4*(r k)^4)*(σ k).real (closedBall (p k) (r k)) :=
      add_le_add (mul_le_mul_of_nonneg_left hvol (by positivity))
        (mul_le_mul_of_nonneg_right hcoef measureReal_nonneg)
    _ = _ := by ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
