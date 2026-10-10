import OAI.Geometry.RCD.Heat.SelectedHarmonicHeatMass
import OAI.Geometry.RCD.Coordinates.NormalizedHeatMassLimit

namespace OAI

/-! # Vanishing scaled Bochner mass for the selected actual harmonic heat sequence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem normalized_harmonic_heat_mass (hK : K ≤ 0)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {C : ℝ} (hC : 0 ≤ C)
    (χ : ∀ k, GoodLaplacianCutoff (hausdorff n X) hX.quadratic (p k) (2*r k) C)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (d : ℕ → Lp ℝ 2 (hausdorff n X))
    (hd : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (d k))
    (U : ℕ → X → ℝ) (L A : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k)) (hUc : ∀ k, HasCompactSupport (U k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ A k)
    (hd0 : ∀ k, d k =ᵐ[(hausdorff n X).restrict (ball (p k) (8*r k))] fun _ => 0)
    (hE0 : Tendsto (fun k =>
      (∫ x in closedBall (p k) (4*r k),
        |localGamma (hausdorff n X) hX.quadratic (u k) (u k) x-1| ∂hausdorff n X)/
        (hausdorff n X).real (ball (p k) (8*r k))) atTop (𝓝 0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ (s : ℕ → ℝ) (hs : ∀ k, 0 < s k),
      (∀ k, s k ≤ 1) ∧ Tendsto s atTop (𝓝 0) ∧
      (let w k := heatSobolev m q (s k) (hs k) (SobolevSpace.toLp m q (u k))
       let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
         (-heatGeneratorAt m q (s k-s k/2) (SobolevSpace.toLp m q (u k)))
       Tendsto (fun k => ‖w k-u k‖/r k) atTop (𝓝 0) ∧
       Tendsto (fun k => ‖w k-u k‖/(r k*Real.sqrt (m.real (ball (p k) (8*r k))))) atTop (𝓝 0) ∧
       ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
         (∀ k, IsFiniteMeasure (σ k)) ∧
         (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
         (∀ k (ψ : SobolevSpace m q) (v : X → ℝ), Continuous v → HasCompactSupport v →
           tsupport v ⊆ ball (p k) (6*r k) → SobolevSpace.toLp m q ψ =ᵐ[m] v →
           (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
             weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
             K*weightedGamma m q v (w k) (w k)) ∧
         Tendsto (fun k => (r k)^2*(σ k).real (closedBall (p k) (r k))/
           m.real (ball (p k) (8*r k))) atTop (𝓝 0)) := by
  intro m q
  obtain ⟨s,hs,hs1,hs0,hval,hvalnorm,G,σ,hσ,hG,hrep,hmass⟩ :=
    hX.selected_harmonic_heat_mass hn hK p r hr hC χ u d hd U L A hU hUc hu hA hd0
  refine ⟨s,hs,hs1,hs0,hval,hvalnorm,G,σ,hσ,hG,hrep,?_⟩
  have hm (k : ℕ) : 0 < m.real (ball (p k) (8*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by linarith [hr k])).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  exact normalized_heat_mass_limit r (fun k => m.real (ball (p k) (8*r k)))
    (fun k => ∫ x in closedBall (p k) (4*r k), |localGamma m q (u k) (u k) x-1| ∂m)
    (fun k => m.real (closedBall (p k) (4*r k)))
    (fun k => (σ k).real (closedBall (p k) (r k))) hr hm (fun _ => measureReal_nonneg)
    (fun k => measureReal_mono (closedBall_subset_ball (by linarith [hr k]))
      (hX.finiteOnBounded _ isBounded_ball).ne) hK hr0 hE0 hmass

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
