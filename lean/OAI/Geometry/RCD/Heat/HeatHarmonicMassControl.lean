import OAI.Geometry.RCD.Heat.HeatBochnerCutoffLimit
import OAI.Geometry.RCD.Sobolev.HarmonicCutoffMassBound
import OAI.Geometry.RCD.Heat.HeatLocalSourceConvergence
import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Quantitative small local mass for actual heat regularizations of harmonic functions -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem heat_harmonic_mass_control (hK : K ≤ 0)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (2*R) C)
    {b : ℝ} (hb : 4*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (ht1 : ∀ k, t k ≤ 1)
    (ht0 : Tendsto t atTop (𝓝 0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let f := SobolevSpace.toLp m q u
    let w k := heatSobolev m q (t k) (ht k) f
    let D k := heatSobolevMap m q (t k/2) (half_pos (ht k))
      (-heatGeneratorAt m q (t k-t k/2) f)
    ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
      (∀ k, ∀ (ψ : SobolevSpace m q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
          K*weightedGamma m q v (w k) (w k)) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        (σ k).real (closedBall p R) ≤
          (C/(2*R)^2)/2*(∫ x in closedBall p (4*R), |localGamma m q u u x-c| ∂m)+
          (-K)*((∫ x in closedBall p (4*R), |localGamma m q u u x-c| ∂m)+
            c*m.real (closedBall p (4*R)))+η := by
  intro m q f w D
  obtain ⟨G,σ,hσ,hG,hrep,hmass,hlim⟩ := hX.heat_bochner_cutoff_limit hn p hK
    u d hd U L A hU hUc hu hA hR hC χ t ht ht1 ht0
  obtain ⟨hz₁,hz₂⟩ := χ.harmonic_source_terms_zero m q (by linarith) u d hd0
  rw [hz₁,hz₂,add_zero,add_zero] at hlim
  have hbound := χ.energy_error_mass_bound m q (show 0 < 2*R by positivity) hC hK u c
  rw [show 2*(2*R)=4*R by ring] at hbound
  refine ⟨G,σ,hσ,hG,hrep,?_⟩
  intro η hη
  filter_upwards [Metric.tendsto_nhds.mp hlim η hη] with k hk
  have he := (abs_lt.mp (show |(∫ x, χ.weight x ∂σ k)-
    ((1/2:ℝ)*weightedGamma m q χ.laplacian u u-K*weightedGamma m q χ.weight u u)| < η by
      simpa only [Real.dist_eq] using hk)).2
  exact (hmass k).trans (by linarith only [he,hbound])

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
