import OAI.Geometry.RCD.Heat.ScaledHeatPlanVariation
import OAI.Geometry.RCD.Coordinates.NormalizedHeatMeanLimit
import OAI.Geometry.RCD.Harmonic.ScaledAffineMeanLimit

namespace OAI

/-! # Original normalized means become affine from the actual heat family -/

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
theorem scaled_heat_affine_plan (p₀ : X) (hK : K ≤ 0)
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
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (U : ℕ → X → ℝ) (hU : ∀ k, Continuous (U k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (A : ℕ → ℝ≥0) (hA : ∀ k, ∀ᵐ x ∂hausdorff n X,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ A k)
    (M : ℝ≥0)
    (hLip : ∀ k, LipschitzWith M (fun t : Time => (∫ γ, U k (γ t) ∂π k)/r k))
    (HGram : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)] :
    let m := hausdorff n X
    let q := hX.quadratic
    let w k := heatSobolev m q (s k) (hs k) (SobolevSpace.toLp m q (u k))
    let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
      (-heatGeneratorAt m q (s k-s k/2) (SobolevSpace.toLp m q (u k)))
    (∀ k, SobolevSpace.toLp m q (HGram k) =ᵐ[m] localGamma m q (w k) (w k)) →
    (∀ k (ψ : SobolevSpace m q) (b : X → ℝ), Continuous b → HasCompactSupport b →
      tsupport b ⊆ ball (p k) (2*r k) → SobolevSpace.toLp m q ψ =ᵐ[m] b →
      (∫ x, b x ∂σ k)=-(1/2:ℝ)*energyForm m q (HGram k) ψ-
        weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
        K*weightedGamma m q b (w k) (w k)) →
    Tendsto (fun k => (r k)^2*(σ k).real (closedBall (p k) (r k))/
      m.real (ball (p k) (8*r k))) atTop (𝓝 0) →
    Tendsto (fun k => ‖w k-u k‖/(r k*Real.sqrt (m.real (ball (p k) (8*r k)))))
      atTop (𝓝 0) →
    ∀ t : Time, Tendsto (fun k => ((∫ γ, U k (γ t) ∂π k)-
      ((1-(t:ℝ))*(∫ γ, U k (γ 0) ∂π k)+(t:ℝ)*(∫ γ, U k (γ 1) ∂π k)))/r k)
      atTop (𝓝 0) := by
  intro m q w D hGram hσ hmass hval t
  let H k z := if ht : z∈Ioo (0:ℝ) 1 then
    ∫ x, kernelHeat m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k))
      (s k) (SobolevSpace.toLp m q (u k)) x ∂(π k).map
        (fun γ => γ (⟨z,ht.1.le,ht.2.le⟩ : Time)) else 0
  let F k z := if ht : z∈Icc (0:ℝ) 1 then
    ∫ γ, U k (γ (⟨z,ht⟩ : Time)) ∂π k else 0
  obtain ⟨G,hder,hint,hG⟩ := hX.scaled_heat_plan_variation hn p₀ hK p r s hr hs
    π hgeo hopt hB hcomp hs₀ hs₁ (fun k => SobolevSpace.toLp m q (u k)) A hA
    HGram σ hGram hσ hmass
  have hFLip (k : ℕ) : LipschitzOnWith M (fun z => F k z/r k) (Icc (0:ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simpa only [F,dite_eq_left ha,dite_eq_left hb,Subtype.dist_eq] using
      (hLip k).dist_le_mul (⟨a,ha⟩ : Time) (⟨b,hb⟩ : Time)
  have hm (k : ℕ) : 0 < m.real (ball (p k) (8*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by linarith [hr k])).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  let ν k (z : Time) := (π k).map (fun γ => γ z)
  have hlim := normalized_heat_means_limit m q
    (fun k => hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k))
    r (fun k => m.real (ball (p k) (8*r k))) hr hm ν hB hcomp u U hu s hs hval
  have hmean : ∀ z∈Ioo (0:ℝ) 1, Tendsto (fun k => (F k z-H k z)/r k) atTop (𝓝 0) := by
    intro z hz
    let z' : Time := ⟨z,hz.1.le,hz.2.le⟩
    have hzI : z∈Icc (0:ℝ) 1 := z'.property
    have he (k : ℕ) : (∫ x, U k x ∂ν k z')=∫ γ, U k (γ z') ∂π k :=
      integral_map (measurable_path_eval z').aemeasurable (hU k).aestronglyMeasurable
    convert (hlim.tendsto_at z').neg using 1
    · funext k
      dsimp only [F,H]
      rw [dite_eq_left hzI,dite_eq_left hz,he]
      ring
    · simp
  have hh := scaled_affine_mean_limit F H G r hr M hFLip hder hint hG hmean t.property
  have he (k : ℕ) (z : Time) : F k z=∫ γ, U k (γ z) ∂π k := by
    dsimp only [F]
    rw [dite_eq_left z.property]
  have he0 (k : ℕ) : F k 0=∫ γ, U k (γ 0) ∂π k := he k 0
  have he1 (k : ℕ) : F k 1=∫ γ, U k (γ 1) ∂π k := he k 1
  simpa only [he,he0,he1] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
