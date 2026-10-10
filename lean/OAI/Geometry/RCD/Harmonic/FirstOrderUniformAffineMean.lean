import OAI.Geometry.RCD.Harmonic.FirstOrderAbsoluteAffineMean
import OAI.Geometry.RCD.Harmonic.FirstOrderCompactRepresentative
import OAI.Geometry.RCD.Harmonic.PathAffineResidual

namespace OAI

/-! # Mean uniform path defects for the original splitting coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_uniform_affine_mean {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K*(16*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) ((π k).map (fun γ => (γ 0,γ 1))))
    {B : ℝ} (hB : 0 ≤ B)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t) ≤
      ENNReal.ofReal (B/(hausdorff n X).real (ball (p k) (4*r k))) • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k) ≤ r k/12)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k) ≤ r k/12)
    (i : Fin n) :
    ∃ F : ℕ → C(Time,X) → C(Time,ℝ),
      (∀ k, Continuous (F k)) ∧
      (∀ k, ∀ᵐ γ ∂π k, ∀ t : Time, F k γ t=
        (v k (γ t) i-((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i))/r k) ∧
      (∀ k, Integrable (fun γ => ‖F k γ‖) (π k)) ∧
      Tendsto (fun k => ∫ γ, ‖F k γ‖ ∂π k) atTop (𝓝 0) := by
  let := hX.separable
  choose V L A hV hVc hA hEq hloc using fun k =>
    hX.first_order_compact_representative hn (hr k) (hε k) (hε1 k) (u k) (v k) (hsplit k) i
  let F k γ := pathAffineResidual (V k) (r k) γ
  have hF (k : ℕ) : Continuous (F k) := pathAffineResidual_continuous (V k) (r k)
  have hbound (k : ℕ) := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
    ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
    (by linarith [hr k] : 0 ≤ r k/12) (hs₀ k) (hs₁ k)
  have hnorm (k : ℕ) (γ : C(Time,X)) : ‖F k γ‖ ≤ 3*(A k:ℝ)/r k :=
    pathAffineResidual_norm_le (V k) (hr k) (A k).coe_nonneg (hA k) γ
  have hI (k : ℕ) : Integrable (fun γ => ‖F k γ‖) (π k) :=
    Integrable.of_bound (hF k).norm.aestronglyMeasurable (3*(A k:ℝ)/r k)
      (Eventually.of_forall fun γ => by simpa only [norm_norm] using hnorm k γ)
  have hEval (k : ℕ) (z : Time) : Integrable (fun γ => F k γ z) (π k) :=
    Integrable.of_bound ((continuous_eval_const z).comp (hF k)).aestronglyMeasurable
      (3*(A k:ℝ)/r k) (Eventually.of_forall fun γ =>
        ((F k γ).norm_coe_le_norm z).trans (hnorm k γ))
  have hLip (k : ℕ) : ∀ᵐ γ ∂π k, LipschitzWith 4 (F k γ) := by
    filter_upwards [hbound k] with γ hγ
    have hs : ∀ z : Time, γ z∈ball (p k) (r k/2) := fun z =>
      (hγ.2 z).trans_lt (by linarith [hr k])
    have hlen : dist (γ 0) (γ 1) ≤ (1:ℝ≥0)*r k := by
      have ht := dist_triangle (γ 0) (p k) (γ 1)
      rw [dist_comm (p k) (γ 1)] at ht
      norm_num only [NNReal.coe_one,one_mul]
      linarith [hγ.2 0,hγ.2 1,hr k]
    simpa only [mul_one,show (2:ℝ≥0)*2=4 by norm_num] using
      pathAffineResidual_lipschitz (V k) (hr k) γ hγ.1 hs (hloc k) hlen
  have heq (k : ℕ) : ∀ᵐ γ ∂π k, ∀ z : Time, F k γ z=
      (v k (γ z) i-((1-(z:ℝ))*v k (γ 0) i+(z:ℝ)*v k (γ 1) i))/r k := by
    filter_upwards [hbound k] with γ hγ z
    have hs (t : Time) : V k (γ t)=v k (γ t) i :=
      hEq k ((hγ.2 t).trans_lt (by linarith [hr k]))
    simp only [F,pathAffineResidual_apply,hs]
  have hpt (z : Time) : Tendsto (fun k => ∫ γ, |F k γ z| ∂π k) atTop (𝓝 0) := by
    have hlim := hX.first_order_absolute_affine_mean hn hK p r ε hr hr0 hcurv
      hε hε1 hε0 u v hsplit π hgeo hopt hB hcomp hs₀ hs₁ i z
    have he (k : ℕ) : (∫ γ, |F k γ z| ∂π k)=
        (∫ γ, |v k (γ z) i-((1-(z:ℝ))*v k (γ 0) i+(z:ℝ)*v k (γ 1) i)| ∂π k)/r k := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [heq k] with γ hγ
      rw [hγ z,abs_div,abs_of_pos (hr k)]
    simpa only [he] using hlim
  exact ⟨F,hF,heq,hI,time_uniform_mean_limit π F 4 hI hEval hLip hpt⟩

end RegularPointCoordinates

end

end OAI
