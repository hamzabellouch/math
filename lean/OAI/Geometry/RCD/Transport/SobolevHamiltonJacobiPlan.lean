import OAI.Geometry.RCD.Transport.HamiltonJacobiPlanBound
import OAI.Geometry.RCD.Transport.TestPlanMeanSlope

namespace OAI

/-! # Endpoint comparison from the Sobolev Hamilton--Jacobi inequality

The temporal difference is differentiated in L2. The spatial difference
uses a fixed Sobolev function and the test-plan slope bound. A one-sided
mean-value theorem combines them without evaluating null sets on a diagonal.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem sobolev_hamilton_jacobi_plan_comparison
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ t ∈ Ico a b, ∀ᵐ γ ∂π, geodesicExtension γ t ∈ S)
    (u : ℝ → SobolevSpace μ Q) (hu : ContinuousOn u (Icc a b))
    (D : ℝ → Lp ℝ 2 μ)
    (hder : ∀ t ∈ Ico a b, HasDerivAt (fun s => SobolevSpace.toLp μ Q (u s)) (D t) t)
    (hgrad : ∀ t ∈ Ico a b, ∀ᵐ x ∂μ.restrict S,
      (SobolevSpace.minimalSlope μ Q (u t) x)^2 ≤ 2*D t x) :
    (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u a) (geodesicExtension γ a) ∂π) -
      (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u b) (geodesicExtension γ b) ∂π) ≤
      (b-a)*(∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/2 := by
  let T := testPlanMeanCLM μ π hC hcomp
  let U := fun t => SobolevSpace.toLp μ Q (u t)
  let A := fun t => T t (U t)
  let E := (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/2
  have hT : Continuous (fun q : Lp ℝ 2 μ × ℝ => T q.2 q.1) :=
    testPlanMeanCLM_jointly_continuous μ π hgeo hC hcomp hLength
  have hU : ContinuousOn U (Icc a b) := (SobolevSpace.toLpCLM μ Q).continuous.comp_continuousOn hu
  have hA : ContinuousOn (fun t => -A t) (Icc a b) :=
    (hT.comp_continuousOn (hU.prodMk continuousOn_id)).neg
  have hB : ContinuousOn (fun t => -A a+E*(t-a)) (Icc a b) := by fun_prop
  have hBder (x : ℝ) (_ : x ∈ Ico a b) :
      HasDerivWithinAt (fun t => -A a+E*(t-a)) E (Ici x) x := by
    simpa only [mul_one,id_eq] using
      ((((hasDerivAt_id x).sub_const a).const_mul E).const_add (-A a)).hasDerivWithinAt (s := Ici x)
  have hright (x : ℝ) (hx : x ∈ Ico a b) (r : ℝ) (hr : E < r) :
      ∃ᶠ t in 𝓝[>] x, slope (fun q => -A q) x t < r := by
    let s : Time := ⟨x,⟨ha.trans hx.1,hx.2.le.trans hb⟩⟩
    let F := ∫ γ : C(Time,X), dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q (u x) (γ s) ∂π
    have hact : F-T x (D x) ≤ E := by
      have hh := hamilton_jacobi_plan_bound μ Q π hC hcomp hLength (u x) (D x) s hS
        (by
          filter_upwards [hs x hx] with γ hγ
          rw [← geodesicExtension_eq γ s]
          exact hγ) (hgrad x hx)
      have he : T x (D x) = ∫ γ : C(Time,X), D x (γ s) ∂π := by
        dsimp only [T]
        rw [testPlanMeanCLM_apply]
        exact integral_congr_ae (Eventually.of_forall fun γ => by
          change D x (geodesicExtension γ x) = D x (γ s)
          rw [show geodesicExtension γ x = γ s from geodesicExtension_eq γ s])
      have hh' : -E ≤ (∫ γ : C(Time,X), D x (γ s) ∂π)-F := by
        dsimp only [E,F]
        linarith [hh]
      rw [← he] at hh'
      linarith
    let ε := (r-E)/4
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have ht := moving_linear_difference_tendsto T U hT.continuousAt (hder x hx)
    have hfilt : 𝓝[>] x ≤ 𝓝[≠] x := nhdsWithin_mono x (fun t ht => ne_of_gt ht)
    have ht' : ∀ᶠ t in 𝓝[>] x, T x (D x)-ε <
        (t-x)⁻¹*(T t (U t)-T t (U x)) :=
      (ht.mono_left hfilt).eventually (lt_mem_nhds (sub_lt_self _ hε))
    have hs' := testPlanMeanCLM_right_slope_bound μ Q π hgeo hC hcomp hLength (u x) s
      (hx.2.trans_le hb) hε
    have hevent : ∀ᶠ t in 𝓝[>] x, slope (fun q => -A q) x t < r := by
      filter_upwards [ht',hs'] with t ht hs'
      have heq : slope (fun q => -A q) x t =
          -((t-x)⁻¹*(T t (U t)-T t (U x))) -
          (T t (U x)-T x (U x))/(t-x) := by
        dsimp only [A]
        rw [slope_fun_def_field]
        ring
      have hneg := neg_le_abs ((T t (U x)-T x (U x))/(t-x))
      change |(T t (U x)-T x (U x))/(t-x)| < F+ε at hs'
      rw [heq]
      dsimp only [ε] at ht hs'
      linarith
    exact hevent.frequently
  have hend := image_le_of_liminf_slope_right_le_deriv_boundary hA
    (B := fun t => -A a+E*(t-a)) (B' := fun _ => E)
    (by simp) hB hBder hright (x := b) ⟨hab,le_rfl⟩
  change -A b ≤ -A a+E*(b-a) at hend
  have he : A a-A b ≤ (b-a)*E := by linarith
  simpa only [A,T,U,testPlanMeanCLM_apply,E,mul_div_assoc] using he

end RegularPointCoordinates

end

end OAI
