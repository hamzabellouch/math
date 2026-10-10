import OAI.Geometry.RCD.Heat.HeatVarianceContinuity
import OAI.Geometry.RCD.Sobolev.VarianceLowerBound

namespace OAI

/-! # An integrated reverse Poincaré estimate from the actual RCD heat flow -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The heat variance controls the gradient, with a uniform sufficient
short-time curvature factor. The initial data are compact Lipschitz. -/
theorem NoncollapsedRCD.heat_variance_lower
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hφs : HasCompactSupport φ)
    (p : X) (f w : Lp ℝ 2 (hausdorff n X)) (hφf : φ =ᵐ[hausdorff n X] f)
    (C B : ℝ≥0) (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    (hw : 0 ≤ w) (hwB : ∀ᵐ x ∂hausdorff n X, |w x| ≤ B)
    (T : ℝ) (hT : 0 < T) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    2*T*Real.exp (-2*|K| *T)*
        (∫ x, w x*(SobolevSpace.minimalSlope μ hX.quadratic
          (heatSobolev μ hX.quadratic T hT f) x)^2 ∂μ) ≤
      (∫ x, heatAt μ hX.quadratic T w x*(f x)^2 ∂μ)-
        (∫ x, w x*(heatAt μ hX.quadratic T f x)^2 ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  let E := ∫ x, w x*(SobolevSpace.minimalSlope μ hX.quadratic
    (heatSobolev μ hX.quadratic T hT f) x)^2 ∂μ
  have hE : 0 ≤ E := by
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr hw] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hd : ∀ s ∈ Ioo 0 T, ∃ G : ℝ,
      HasDerivAt (heatSquarePairing μ hX.quadratic f w C hf T) (2*G) s ∧
      E ≤ Real.exp (-2*K*s)*G := by
    intro s hs
    have hTs : 0 < T-s := sub_pos.mpr hs.2
    let U := heatSobolev μ hX.quadratic (T-s) hTs f
    let G := ∫ x, heatAt μ hX.quadratic s w x*
      (SobolevSpace.minimalSlope μ hX.quadratic U x)^2 ∂μ
    refine ⟨G,?_,?_⟩
    · let A : ℝ≥0 := ⟨(L:ℝ)*Real.exp (-K*(T-s)),
        mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
      have hgrad : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic U x ≤ A :=
        hX.heat_compact_slope_bdd K n hn hφ hφs p f hφf (T-s) hTs
      exact heatSquarePairing_hasDerivAt μ hX.quadratic f w C B A hf hwB T s hs.1 hTs hgrad
    · have hbe := hX.heat_weighted_gradient K n hn p U w hw B hwB hs.1
      have heq := heatSobolev_iterate μ hX.quadratic f s (T-s) hs.1 hTs
      simp only [show s+(T-s)=T by ring] at heq
      rw [heq] at hbe
      exact hbe
  have hh := variance_lower_bound hT hE
    (heatSquarePairing_continuous μ hX.quadratic f w C hf T).continuousOn hd
  rw [heatSquarePairing_eq_integral,heatSquarePairing_eq_integral] at hh
  simpa only [sub_self,sub_zero,heatAt_zero,one_apply_eq_self] using hh

end RegularPointCoordinates

end

end OAI
