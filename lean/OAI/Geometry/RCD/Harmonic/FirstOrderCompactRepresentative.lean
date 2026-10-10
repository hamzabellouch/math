import OAI.Geometry.RCD.Coordinates.RegularCoreRepresentative
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.SplittingApproximation
import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound

namespace OAI

/-! # Compact continuous representatives of the original local coordinates -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_compact_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v) (i : Fin n) :
    ∃ (V : C(X,ℝ)) (L A : ℝ≥0), LipschitzWith L V ∧ HasCompactSupport V ∧
      (∀ x, |V x| ≤ A) ∧ EqOn V (fun x => v x i) (ball p (6*r)) ∧
      LipschitzOnWith 2 V (ball p (r/2)) := by
  let m := hausdorff n X
  let q := hX.quadratic
  let := hX.openPos K n
  let ℓ : ℝ≥0 := ⟨1+ε,by linarith⟩
  obtain ⟨g,d,_hd,hrep,_hd0⟩ := hX.local_poisson_regular_extension hn (u i) 0
    (show 0 < 6*r by linarith) (show 2*(6*r)<16*r by linarith)
    ((isConstantLaplacianOn_zero_iff m q _ _).mpr (hs.harmonic i)) ℓ (hs.gradient i)
  obtain ⟨V,L,_A,hV,hVc,hg,_hA⟩ := regular_core_representative m q g
  obtain ⟨A,hA⟩ := hVc.exists_bound_of_continuous hV.continuous
  let A' : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  have hsmall : ball p (6*r) ⊆ ball p (16*r) := ball_subset_ball (by linarith)
  have h1 : V =ᵐ[m.restrict (ball p (6*r))] SobolevSpace.toLp m q g.val :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae hg)
  have h2 : SobolevSpace.toLp m q g.val =ᵐ[m.restrict (ball p (6*r))] fun x => v x i :=
    hrep.trans (ae_restrict_of_ae_restrict_of_subset hsmall (hs.representative i))
  have hEq := Measure.eqOn_open_of_ae_eq (h1.trans h2) isOpen_ball hV.continuous.continuousOn
    (((EuclideanSpace.proj i).continuous.comp_continuousOn hs.continuous).mono hsmall)
  refine ⟨⟨V,hV.continuous⟩,L,A',hV,hVc,?_,hEq,?_⟩
  · intro x
    exact (show |V x| ≤ A by simpa only [Real.norm_eq_abs] using hA x).trans (le_max_left _ _)
  · have h4 : ball p (8*(r/2)) ⊆ ball p (6*r) := ball_subset_ball (by linarith)
    have he := ae_restrict_of_ae_restrict_of_subset h4 (localGamma_pair_congr_ae m q hrep hrep)
    have hgrad := ae_restrict_of_ae_restrict_of_subset
      (h4.trans hsmall) (hs.gradient i)
    apply hX.continuous_local_gradient_lipschitz hn g.val V p (half_pos hr) 2
      hV.continuous.continuousOn (ae_restrict_of_ae hg)
    filter_upwards [he,hgrad] with x hx hy
    rw [hx]
    norm_num only [NNReal.coe_ofNat]
    nlinarith

end RegularPointCoordinates

end

end OAI
