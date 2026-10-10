import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.LocalizedPoissonRepresentative
import OAI.Geometry.RCD.Sobolev.PoissonCutoffSource

namespace OAI

/-! # Constructing the local representative of an actual Poisson solution -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Localizing the equation and integrating its actual two source terms
constructs a Lipschitz representative without a gradient premise on `f`. -/
theorem NoncollapsedRCD.cutoff_poisson_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ J : ℝ, 0 < J ∧ ∀ (p : X) (R T C : ℝ), 0 < R → -1 ≤ K*R^2 →
      0 < T → T ≤ 1 → T ≤ R^2 → 0 ≤ C →
      ∀ (Ω : Set X) (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ),
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c →
      ∀ (A : ℝ≥0), (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ f x| ≤ A) →
      ∀ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C,
      closedBall p (2*R) ⊆ Ω →
      ∃ v : X → ℝ,
        LipschitzWith (Real.exp (|K| *T)*(A/Real.sqrt T+2*(|c|+A*(C/R^2))*Real.sqrt T)+
          (J/(R*(hausdorff n X).real (ball p R))*
            (∫ z, |2*localGamma (hausdorff n X) hX.quadratic f χ.sobolev z|
              ∂hausdorff n X))*T).toNNReal v ∧
        SobolevSpace.toLp _ _ f =ᵐ[(hausdorff n X).restrict (ball p (R/8))] v := by
  obtain ⟨J,hJ,hrep⟩ := hX.localized_poisson_representative hn hk hg
  refine ⟨J,hJ,?_⟩
  intro p R T C hR hcurv hT hT1 hTR hC Ω f c hf A hA χ hΩ
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have habs (x : X) : |χ.weight x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (χ.bounds x).1]
    exact (χ.bounds x).2
  let u := SobolevSpace.cutoffCLM μ hX.quadratic χ.lipschitz
    (χ.hasCompactSupport μ hX.quadratic) habs (fun x => (χ.bounds x).1) f
  have hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ A := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz
      (χ.hasCompactSupport μ hX.quadratic) habs (fun x => (χ.bounds x).1) f,hA] with x hx ha
    change SobolevSpace.toLp μ hX.quadratic u x = _ at hx
    rw [hx,abs_mul]
    exact (mul_le_mul_of_nonneg_right (habs x) (abs_nonneg _)).trans (by simpa using ha)
  obtain ⟨b,e,heq,hb,hei,herep,hes⟩ :=
    hf.cutoff_source_decomposition μ hX.quadratic f c A hA hR hC χ hΩ
  let D : ℝ≥0 := ⟨|c|+A*(C/R^2),by positivity⟩
  obtain ⟨v,hv,huv⟩ := hrep p R T hR hcurv hT hT1 hTR u b e heq A D hu hb hei hes
  have heint : (∫ z, |e z| ∂μ) = ∫ z, |2*localGamma μ hX.quadratic f χ.sobolev z| ∂μ := by
    apply integral_congr_ae
    filter_upwards [herep] with x hx
    rw [hx]
  refine ⟨v,?_,?_⟩
  · simpa only [heint,D,NNReal.coe_mk,μ] using! hv
  · have hfu : SobolevSpace.toLp μ hX.quadratic f =ᵐ[μ.restrict (ball p (R/8))]
        SobolevSpace.toLp μ hX.quadratic u := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz
          (χ.hasCompactSupport μ hX.quadratic) habs (fun x => (χ.bounds x).1) f)] with x hx he
      have hxR : x ∈ ball p R := by
        have hdist : dist x p < R/8 := hx
        change dist x p < R
        linarith
      change SobolevSpace.toLp μ hX.quadratic u x = _ at he
      rw [χ.one x hxR,one_mul] at he
      exact he.symm
    exact hfu.trans huv

end RegularPointCoordinates

end

end OAI
