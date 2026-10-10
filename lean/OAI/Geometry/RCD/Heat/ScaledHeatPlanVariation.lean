import OAI.Geometry.RCD.Heat.BoundedPlanHeatSecondVariation
import OAI.Geometry.RCD.Heat.CenteredActionRadiusBound
import OAI.Geometry.RCD.Heat.ScaledHeatHessianLimit
import OAI.Geometry.RCD.Transport.ScaledPlanHessianLimit

namespace OAI

/-! # Vanishing second variation on the original compressed plans -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem scaled_heat_plan_variation (p₀ : X) (hK : K ≤ 0)
    (p : ℕ → X) (r s : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hs : ∀ k, 0 < s k)
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) ((π k).map (fun γ => (γ 0,γ 1))))
    {B : ℝ} (hB : 0 ≤ B)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t) ≤
      ENNReal.ofReal (B/(hausdorff n X).real (ball (p k) (8*r k))) • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k) ≤ r k/6)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k) ≤ r k/6)
    (f : ℕ → Lp ℝ 2 (hausdorff n X)) (A : ℕ → ℝ≥0)
    (hf : ∀ k, ∀ᵐ x ∂hausdorff n X, |f k x| ≤ A k)
    (HGram : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)] :
    let m := hausdorff n X
    let q := hX.quadratic
    let w k := heatSobolev m q (s k) (hs k) (f k)
    let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
      (-heatGeneratorAt m q (s k-s k/2) (f k))
    (∀ k, SobolevSpace.toLp m q (HGram k) =ᵐ[m] localGamma m q (w k) (w k)) →
    (∀ k (ψ : SobolevSpace m q) (b : X → ℝ), Continuous b → HasCompactSupport b →
      tsupport b ⊆ ball (p k) (2*r k) → SobolevSpace.toLp m q ψ =ᵐ[m] b →
      (∫ x, b x ∂σ k)=-(1/2:ℝ)*energyForm m q (HGram k) ψ-
        weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
        K*weightedGamma m q b (w k) (w k)) →
    Tendsto (fun k => (r k)^2*(σ k).real (closedBall (p k) (r k))/
      m.real (ball (p k) (8*r k))) atTop (𝓝 0) →
    let H k := kernelHeat m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)) (s k) (f k)
    let F k t := if ht : t∈Ioo (0:ℝ) 1 then
      ∫ x, H k x ∂(π k).map (fun γ => γ (⟨t,ht.1.le,ht.2.le⟩ : Time)) else 0
    ∃ G : ℕ → ℝ → ℝ,
      (∀ k t, t∈Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t) ∧
      (∀ k a b, 0 < a → a ≤ b → b < 1 →
        (∫ t in a..b, G k t)=deriv (F k) b-deriv (F k) a) ∧
      ∀ a b, 0 < a → a ≤ b → b < 1 →
        TendstoUniformlyOn (fun k t => G k t/r k) (fun _ => 0) atTop (Icc a b) := by
  intro m q w D hGram hσ hmass H F
  have hm (k : ℕ) : 0 < m.real (ball (p k) (8*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by linarith [hr k])).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  choose G hder _hLip hident hint using fun k =>
    hX.bounded_plan_heat_second_variation hn p₀ (p k) hK (π k) (hgeo k) (hopt k)
      ENNReal.ofReal_ne_top (hcomp k) (by linarith [hr k] : 0 ≤ r k/6) (hr k)
      (by linarith) (hs₀ k) (hs₁ k) (f k) (A k) (hf k) (hs k)
  refine ⟨G,hder,fun k a b ha hab hb => (hint k a b ha hab hb).2,?_⟩
  intro a b ha hab hb
  let Y := Icc a b
  let δ := a/2
  have hδ : 0 < δ := half_pos ha
  have ht (y : Y) : (y:ℝ)∈Ioo δ 1 :=
    ⟨(show δ < a by dsimp only [δ]; linarith).trans_le y.property.1,y.property.2.trans_lt hb⟩
  let L (k : ℕ) : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| *
    (16*hX.centeredActionBound hn p₀*(r k/6+32*r k)^2/(δ/2)^2)),Real.sqrt_nonneg _⟩
  choose v V J hV hVc hv hVb hcan hGi using fun k (y : Y) => hident k δ hδ y (ht y)
  let Av k : ℝ≥0 := ⟨2*r k*(L k:ℝ),mul_nonneg
    (mul_nonneg (by norm_num) (hr k).le) (L k).coe_nonneg⟩
  have hAv (k : ℕ) (y : Y) : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (v k y) x| ≤ Av k := by
    filter_upwards [hv k y] with x hx
    rw [hx]
    exact hVb k y x
  let M := 3*Real.sqrt (Real.exp |K| * (16*hX.centeredActionBound hn p₀*33^2/(δ/2)^2))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hL (k : ℕ) : ((3*L k:ℝ≥0):ℝ) ≤ M*r k := by
    exact centered_action_radius_bound (hX.centeredActionBound_pos hn p₀).le
      (by linarith [hr k] : 0 ≤ r k/6) (by linarith [hr k]) (hr k)
  let φ k := radialCutoff (p k) (r k/2)
  have hφ (k : ℕ) : AEStronglyMeasurable (φ k) m :=
    (radialCutoff_lipschitz (p k) (half_pos (hr k))).continuous.aestronglyMeasurable
  have hφb (k : ℕ) : ∀ᵐ x ∂m, |φ k x| ≤ (1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds (p k) (r k/2) x).1]
    exact (radialCutoff_bounds (p k) (r k/2) x).2
  have hL1 := hX.scaled_heat_hessian_limit hn hK p r s hr hs f A hf HGram σ v V
    (fun k => 3*L k) (fun k _ => Av k) hV hVc hv hAv hM hL φ hφ hφb
    hGram hσ hmass J hcan
  let ν (k : ℕ) (y : Y) := ((π k).map (fun γ => γ (⟨y,(ha.trans_le y.property.1).le,
    (y.property.2.trans_lt hb).le⟩ : Time))).restrict (closedBall (p k) (r k))
  have hν (k : ℕ) (y : Y) : ν k y ≤ ENNReal.ofReal (B/m.real (ball (p k) (8*r k))) •
      m.restrict (closedBall (p k) (r k)) := by
    simpa only [Measure.restrict_smul] using
      Measure.restrict_mono (subset_refl (closedBall (p k) (r k))) (hcomp k _)
  have hpair := scaled_plan_hessian_limit m (fun k => closedBall (p k) (r k))
    r (fun k => m.real (ball (p k) (8*r k))) hr hm ν hB hν J hL1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  filter_upwards [(Metric.tendstoUniformly_iff.mp hpair) (4*e) (by positivity)] with k hk t ht'
  let y : Y := ⟨t,ht'⟩
  have hh := hk y
  rw [dist_zero_left,Real.norm_eq_abs] at hh
  have heq : G k t/r k=(1/4:ℝ)*((∫ x, J k y x ∂ν k y)/r k) := by
    rw [hGi k y]
    ring
  rw [dist_zero_left,Real.norm_eq_abs,heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
  linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
