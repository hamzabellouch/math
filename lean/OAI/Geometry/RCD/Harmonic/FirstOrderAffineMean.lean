import OAI.Geometry.RCD.Heat.FirstOrderHeatMass
import OAI.Geometry.RCD.Heat.ScaledHeatAffinePlan
import OAI.Geometry.RCD.Transport.LocalLipschitzPlanMean
import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound

namespace OAI

/-! # Affine mean limits for the original first-order splitting coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_affine_mean {K : ℝ} {n : ℕ}
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
    (i : Fin n) (t : Time) :
    Tendsto (fun k => ((∫ γ, v k (γ t) i ∂π k)-
      ((1-(t:ℝ))*(∫ γ, v k (γ 0) i ∂π k)+(t:ℝ)*(∫ γ, v k (γ 1) i ∂π k)))/r k)
      atTop (𝓝 0) := by
  let m := hausdorff n X
  let q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded m hX.finiteOnBounded
  let a k := r k/2
  have ha (k : ℕ) : 0 < a k := half_pos (hr k)
  obtain ⟨g,V,L,A,hV,hVc,hg,hA,hrep,s,hs,hs1,hs0,hval,hvalnorm,G,σ,hσ,hG,hsrc,hmass⟩ :=
    hX.first_order_heat_mass hn hK p r ε hr hr0 hcurv hε hε0 u v hsplit i
  let (k : ℕ) : IsFiniteMeasure (σ k) := hσ k
  have hcomp' (k : ℕ) (z : Time) : (π k).map (fun γ => γ z) ≤
      ENNReal.ofReal (B/m.real (ball (p k) (8*a k))) • m := by
    simpa only [a,show ∀ k,8*(r k/2)=4*r k from fun k => by ring] using hcomp k z
  have hs₀' (k : ℕ) : ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k) ≤ a k/6 := by
    simpa only [a,show ∀ k,(r k/2)/6=r k/12 from fun k => by ring] using hs₀ k
  have hs₁' (k : ℕ) : ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k) ≤ a k/6 := by
    simpa only [a,show ∀ k,(r k/2)/6=r k/12 from fun k => by ring] using hs₁ k
  have hbounded (k : ℕ) := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
    ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
    (by linarith [ha k] : 0 ≤ a k/6) (hs₀' k) (hs₁' k)
  have hloc (k : ℕ) : LipschitzOnWith 2 (V k) (ball (p k) (a k)) := by
    have hsmall : ball (p k) (8*a k) ⊆ ball (p k) (6*r k) :=
      ball_subset_ball (by dsimp only [a]; linarith [hr k])
    have he := ae_restrict_of_ae_restrict_of_subset hsmall
      (localGamma_pair_congr_ae m q (hrep k) (hrep k))
    have huGrad := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by dsimp only [a]; linarith [hr k]) :
        ball (p k) (8*a k) ⊆ ball (p k) (16*r k)) ((hsplit k).gradient i)
    apply hX.continuous_local_gradient_lipschitz hn (g k) (V k) (p k) (ha k) 2
      (hV k).continuous.continuousOn (ae_restrict_of_ae (hg k))
    filter_upwards [he,huGrad] with x hx hy
    rw [hx]
    norm_num only [NNReal.coe_ofNat]
    nlinarith [hε k,hε1 k]
  have hmeanLip (k : ℕ) : LipschitzWith 2 (fun z : Time => (∫ γ, V k (γ z) ∂π k)/a k) := by
    obtain ⟨C,hC⟩ := (hVc k).exists_bound_of_continuous (hV k).continuous
    have hI (z : Time) : Integrable (fun γ => V k (γ z)) (π k) :=
      (integrable_const |C|).mono'
        (((hV k).continuous.measurable.comp (measurable_path_eval z)).aestronglyMeasurable)
        (Eventually.of_forall fun γ => (hC (γ z)).trans (le_abs_self C))
    have hstay : ∀ᵐ γ ∂π k, ∀ z : Time, γ z∈ball (p k) (a k) := by
      filter_upwards [hbounded k] with γ hγ z
      exact (hγ.2 z).trans_lt (by linarith [ha k])
    have hlen : ∀ᵐ γ ∂π k, dist (γ 0) (γ 1) ≤ (1:ℝ≥0)*a k := by
      have h0 := ae_of_ae_map (measurable_path_eval 0).aemeasurable (hs₀' k)
      have h1 := ae_of_ae_map (measurable_path_eval 1).aemeasurable (hs₁' k)
      filter_upwards [h0,h1] with γ h0 h1
      have ht := dist_triangle (γ 0) (p k) (γ 1)
      rw [dist_comm (p k) (γ 1)] at ht
      norm_num only [NNReal.coe_one,one_mul]
      linarith [ha k]
    simpa only [mul_one] using normalized_path_mean_lipschitz (π k) (V k) hI (hloc k)
      (hgeo k) hstay (ha k) hlen
  have hsrc' (k : ℕ) (ψ : SobolevSpace m q) (b : X → ℝ)
      (hb : Continuous b) (hc : HasCompactSupport b) (hbs : tsupport b ⊆ ball (p k) (2*a k))
      (hbψ : SobolevSpace.toLp m q ψ =ᵐ[m] b) :=
    hsrc k ψ b hb hc (hbs.trans (ball_subset_ball (by dsimp only [a]; linarith [hr k]))) hbψ
  have hlim := hX.scaled_heat_affine_plan hn (p 0) hK p a s ha hs π hgeo hopt hB hcomp'
    hs₀' hs₁' g V (fun k => (hV k).continuous) hg A hA 2 hmeanLip G σ hG hsrc' hmass hvalnorm t
  have heq (k : ℕ) (z : Time) : (∫ γ, V k (γ z) ∂π k)=∫ γ, v k (γ z) i ∂π k := by
    have hsmall : ball (p k) (6*r k) ⊆ ball (p k) (16*r k) :=
      ball_subset_ball (by linarith [hr k])
    have h1 : V k =ᵐ[m.restrict (ball (p k) (6*r k))] SobolevSpace.toLp m q (g k) :=
      Filter.EventuallyEq.symm (ae_restrict_of_ae (hg k))
    have h2 : SobolevSpace.toLp m q (g k) =ᵐ[m.restrict (ball (p k) (6*r k))]
        fun x => v k x i :=
      (hrep k).trans (ae_restrict_of_ae_restrict_of_subset hsmall ((hsplit k).representative i))
    have hVV := h1.trans h2
    have hh := ((Measure.absolutelyContinuous_of_le_smul (hcomp k z)).restrict
      (ball (p k) (6*r k))).ae_eq hVV
    change ∀ᵐ x ∂((π k).map (fun γ => γ z)).restrict (ball (p k) (6*r k)),
      V k x=v k x i at hh
    rw [ae_restrict_iff' measurableSet_ball] at hh
    have hp := ae_of_ae_map (measurable_path_eval z).aemeasurable hh
    apply integral_congr_ae
    filter_upwards [hp,hbounded k] with γ he hb
    exact he ((hb.2 z).trans_lt (by dsimp only [a]; linarith [hr k]))
  have hh := hlim.const_mul (1/2:ℝ)
  convert hh using 1
  · funext k
    simp only [heq,a]
    ring
  · simp

end RegularPointCoordinates

end

end OAI
