import OAI.Geometry.RCD.Sobolev.ConstantSourceBochnerLimit
import OAI.Geometry.RCD.Sobolev.PoissonCutoffEnergyBound
import OAI.Geometry.RCD.Heat.HeatBochnerCutoffLimit
import OAI.Geometry.RCD.Heat.QuadraticHeatBochnerMass

namespace OAI

/-! # Quantitative shifted mass for the actual heat of a Poisson replacement

The full positive heat Bochner measures are constructed, including singular
mass. Their shifted cutoff integrals have a limit bounded by the original
distance-source energy error and the explicit curvature term.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_heat_shifted_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0) (p : X)
    (u q : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤A)
    {R C b a E : ℝ} (hR : 0<R) (hC : 0≤C) (hb : 4*R<b) (hna : (n:ℝ)≤a)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (2*R) C)
    (hda : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => a)
    (ρ : Measure X)
    (hsource : ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (M : ℝ≥0),
      LipschitzWith M v → HasCompactSupport v → tsupport v ⊆ ball p b →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
      energyForm (hausdorff n X) hX.quadratic q ψ+
        a*(∫ x in ball p b, v x ∂hausdorff n X)=∫ x, v x ∂ρ)
    (heik : (fun x => (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic q q x)
      =ᵐ[(hausdorff n X).restrict (ball p b)] SobolevSpace.toLp (hausdorff n X) hX.quadratic q)
    (herror : (∫ x in ball p b,
      |(1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic u u x-
        (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic q q x| ∂hausdorff n X)≤E)
    (t : ℕ → ℝ) (ht : ∀ k, 0<t k) (ht1 : ∀ k, t k≤1) (ht0 : Tendsto t atTop (𝓝 0)) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let f := SobolevSpace.toLp μ Q u
    let w k := heatSobolev μ Q (t k) (ht k) f
    let D k := heatSobolevMap μ Q (t k/2) (half_pos (ht k))
      (-heatGeneratorAt μ Q (t k-t k/2) f)
    ∃ (G : ℕ → SobolevSpace μ Q) (σ : ℕ → Measure X) (ell : ℝ),
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, SobolevSpace.toLp μ Q (G k) =ᵐ[μ] localGamma μ Q (w k) (w k)) ∧
      (∀ k, ∀ (ψ : SobolevSpace μ Q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
        (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm μ Q (G k) ψ-
          weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) (w k) (D k)-
          K*weightedGamma μ Q v (w k) (w k)) ∧
      Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
        2*(∫ x, χ.weight x*SobolevSpace.toLp μ Q (D k) x ∂μ)+
        (n:ℝ)*(∫ x, χ.weight x ∂μ)) atTop (𝓝 ell) ∧
      ell ≤ (C/(2*R)^2)*E-K*weightedGamma μ Q χ.weight u u := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro μ Q f w D
  obtain ⟨G,σ,hσ,hG,hrep,-,hlim⟩ := hX.heat_bochner_cutoff_limit hn p hK
    u d hd U L A hU hUc hu hA hR hC χ t ht ht1 ht0
  let ell := (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-
    K*weightedGamma μ Q χ.weight u u+(n-2*a)*(∫ x, χ.weight x ∂μ)
  have hconst := χ.constant_source_terms μ Q (by linarith : 2*(2*R)<b) u d hd a hda
  have hlim' : Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop
      (𝓝 ((1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-
        K*weightedGamma μ Q χ.weight u u)) := by
    convert hlim using 1
    congr 1
    linarith only [hconst]
  have hdlim := χ.source_integral_tendsto_constant μ Q (by linarith : 2*(2*R)<b) a hda
    (heat_regularization_value_source_converges μ Q u d hd t ht ht0).2
  have hshift := (hlim'.sub (hdlim.const_mul 2)).add
    (tendsto_const_nhds (x := (n:ℝ)*(∫ x, χ.weight x ∂μ)))
  refine ⟨G,σ,ell,hσ,hG,hrep,?_,?_⟩
  · convert hshift using 1
    congr 1
    dsimp only [ell]
    ring
  · have hbnd := χ.poisson_energy_bound μ Q hC (by linarith : 2*(2*R)<b)
      u q ρ hna hsource heik herror
    dsimp only [ell]
    linarith only [hbnd]

end RegularPointCoordinates

end

end OAI
