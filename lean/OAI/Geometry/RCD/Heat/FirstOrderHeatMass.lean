import OAI.Geometry.RCD.Heat.FirstOrderCompactHeatData
import OAI.Geometry.RCD.Coordinates.NormalizedHarmonicHeatMass
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # A vanishing full-mass heat approximation of each original splitting coordinate -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_heat_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K*(16*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hs : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k)) (i : Fin n) :
    let m := hausdorff n X
    let q := hX.quadratic
    let a k := r k/2
    ∃ (g : ℕ → SobolevSpace m q) (V : ℕ → X → ℝ) (L A : ℕ → ℝ≥0),
      (∀ k, LipschitzWith (L k) (V k)) ∧ (∀ k, HasCompactSupport (V k)) ∧
      (∀ k, SobolevSpace.toLp m q (g k) =ᵐ[m] V k) ∧
      (∀ k, ∀ᵐ x ∂m, |SobolevSpace.toLp m q (g k) x| ≤ A k) ∧
      (∀ k, SobolevSpace.toLp m q (g k) =ᵐ[m.restrict (ball (p k) (6*r k))]
        SobolevSpace.toLp m q (u k i)) ∧
      ∃ (s : ℕ → ℝ) (hs : ∀ k, 0 < s k),
        (∀ k, s k ≤ 1) ∧ Tendsto s atTop (𝓝 0) ∧
        (let w k := heatSobolev m q (s k) (hs k) (SobolevSpace.toLp m q (g k))
         let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
           (-heatGeneratorAt m q (s k-s k/2) (SobolevSpace.toLp m q (g k)))
         Tendsto (fun k => ‖w k-g k‖/a k) atTop (𝓝 0) ∧
         Tendsto (fun k => ‖w k-g k‖/(a k*Real.sqrt (m.real (ball (p k) (8*a k))))) atTop (𝓝 0) ∧
         ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
           (∀ k, IsFiniteMeasure (σ k)) ∧
           (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
           (∀ k (ψ : SobolevSpace m q) (f : X → ℝ), Continuous f → HasCompactSupport f →
             tsupport f ⊆ ball (p k) (6*a k) → SobolevSpace.toLp m q ψ =ᵐ[m] f →
             (∫ x, f x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
               weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
               K*weightedGamma m q f (w k) (w k)) ∧
           Tendsto (fun k => (a k)^2*(σ k).real (closedBall (p k) (a k))/
             m.real (ball (p k) (8*a k))) atTop (𝓝 0)) := by
  intro m q a
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded m hX.finiteOnBounded
  obtain ⟨g,d,V,L,A,hd,hV,hVc,hg,hA,hrep,hd0,herr⟩ :=
    hX.first_order_compact_heat_data hn p r ε hr hcurv hε hε0 u v hs i
  obtain ⟨C,hC,hcut⟩ := hX.goodCutoffInput hn
  have hcutcurv (k : ℕ) : -1 ≤ K*(r k)^2 := by
    apply (hcurv k).trans
    apply mul_le_mul_of_nonpos_left _ hK
    nlinarith [sq_nonneg (r k)]
  let χ (k : ℕ) := Classical.choice (hcut (p k) (r k) (hr k) (hcutcurv k))
  have hχ (k : ℕ) : GoodLaplacianCutoff m q (p k) (2*a k) C := by
    simpa only [a,show 2*(r k/2)=r k by ring] using χ k
  have ha (k : ℕ) : 0 < a k := half_pos (hr k)
  have ha0 : Tendsto a atTop (𝓝 0) := by simpa only [zero_div] using hr0.div_const 2
  have hd0' (k : ℕ) : d k =ᵐ[m.restrict (ball (p k) (8*a k))] fun _ => 0 :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by dsimp only [a]; linarith [hr k])) (hd0 k)
  have herr' : Tendsto (fun k =>
      (∫ x in closedBall (p k) (4*a k), |localGamma m q (g k) (g k) x-1| ∂m)/
        m.real (ball (p k) (8*a k))) atTop (𝓝 0) := by
    simpa only [a,show ∀ k,4*(r k/2)=2*r k from fun k => by ring,
      show ∀ k,8*(r k/2)=4*r k from fun k => by ring] using herr
  refine ⟨g,V,L,A,hV,hVc,hg,hA,hrep,?_⟩
  exact hX.normalized_harmonic_heat_mass hn hK p a ha ha0 (by linarith) hχ
    g d hd V L A hV hVc hg hA hd0' herr'

end RegularPointCoordinates

end

end OAI
