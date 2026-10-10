import OAI.Geometry.NodalSets.Charts.LocalPiolaDivergence
import OAI.Geometry.NodalSets.Charts.SphereTransitionFlux

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hA hs hp hf

lemma sphereCoordFlux_smooth (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (sphereCoordFlux A f p i) :=
  Complex.ofRealCLM.contDiff.comp
    ((intrinsicRoundFlux_smooth A hA hs hp f hf p i).comp seedCoordEquiv.contDiff)

lemma sphereCoordFlux_divergence (p : Base) (x : Coord) :
    complexDivergence (sphereCoordFlux A f p) x =
      ((∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  unfold complexDivergence
  apply Finset.sum_congr rfl
  intro i _
  exact seedCoordPartial_pullback _
    ((intrinsicRoundFlux_smooth A hA hs hp f hf p i).differentiable (by simp)) i x

lemma sphereChartTransition_divergence (p q : Base) {x : Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    complexDivergence (sphereCoordFlux A f p) x =
      (|(jacobian (sphereChartTransition p q) x).det| : ℝ) *
        complexDivergence (sphereCoordFlux A f q) (sphereChartTransition p q x) := by
  have he (i : Fin 4) : sphereCoordFlux A f p i =ᶠ[𝓝 x]
      absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q) i := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact sphereChartTransition_flux A f hf p q hy i
  have hd : complexDivergence (sphereCoordFlux A f p) x =
      complexDivergence (absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q)) x := by
    unfold complexDivergence coordPartial
    apply Finset.sum_congr rfl
    intro i _
    rw [(he i).fderiv_eq]
  rw [hd]
  exact local_absolutePiola_divergence _ (sphereChartTransitionDomain_open p q)
    (sphereChartTransition_smoothOn p q) _ x hx
    (fun i ↦ (sphereCoordFlux_smooth A hA hs hp f hf q i).differentiable (by simp) _)
    (sphereChartTransition_jacobian_ne_zero p q hx)

theorem intrinsicWeightedChartOperator_transition (rho : Base → ℝ) (p q : Base) {x : Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    intrinsicWeightedChartOperator A rho f p (seedCoordEquiv x) =
      intrinsicWeightedChartOperator A rho f q (seedCoordEquiv (sphereChartTransition p q x)) := by
  have hd := sphereChartTransition_divergence A hA hs hp f hf p q hx
  rw [sphereCoordFlux_divergence A hA hs hp f hf,
    sphereCoordFlux_divergence A hA hs hp f hf] at hd
  have hdR : (∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
      |(jacobian (sphereChartTransition p q) x).det| *
        ∑ i, fderiv ℝ (intrinsicRoundFlux A f q i) (seedCoordEquiv (sphereChartTransition p q x))
          (EuclideanSpace.basisFun (Fin 4) ℝ i) := by exact_mod_cast hd
  have hpoint := sphereChartTransition_point p q hx
  have hn := abs_ne_zero.mpr (sphereChartTransition_jacobian_ne_zero p q hx)
  unfold sphereChartCoordMap at hpoint
  simp only [intrinsicWeightedChartOperator,hdR,sphereChartTransition_round_density p q hx,
    hpoint,_root_.mul_inv_rev]
  calc
    _ = (rho ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x)))⁻¹ *
        (roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)))⁻¹ *
        (|(jacobian (sphereChartTransition p q) x).det|⁻¹ *
          |(jacobian (sphereChartTransition p q) x).det|) *
          (∑ i, fderiv ℝ (intrinsicRoundFlux A f q i) (seedCoordEquiv (sphereChartTransition p q x))
            (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn,mul_one]

end
end Yau.Target

end OAI
