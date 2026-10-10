import OAI.Geometry.RCD.Harmonic.FirstOrderAffineMean
import OAI.Geometry.RCD.Transport.HalfRestrictedOptimalPlan

namespace OAI

/-! # Mean absolute affine defects of the original splitting coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_absolute_affine_mean {K : ℝ} {n : ℕ}
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
    Tendsto (fun k => (∫ γ, |v k (γ t) i-
      ((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i)| ∂π k)/r k) atTop (𝓝 0) := by
  let m := hausdorff n X
  let q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded m hX.finiteOnBounded
  let := hX.openPos K n
  obtain ⟨g,d,V,L,A,_hd,hV,hVc,hg,_hA,hrep,_hd0,_herr⟩ :=
    hX.first_order_compact_heat_data hn p r ε hr hcurv hε hε0 u v hsplit i
  have hEq (k : ℕ) : EqOn (V k) (fun x => v k x i) (ball (p k) (6*r k)) := by
    have hsmall : ball (p k) (6*r k) ⊆ ball (p k) (16*r k) :=
      ball_subset_ball (by linarith [hr k])
    have h1 : V k =ᵐ[m.restrict (ball (p k) (6*r k))] SobolevSpace.toLp m q (g k) :=
      Filter.EventuallyEq.symm (ae_restrict_of_ae (hg k))
    have h2 : SobolevSpace.toLp m q (g k) =ᵐ[m.restrict (ball (p k) (6*r k))]
        fun x => v k x i :=
      (hrep k).trans (ae_restrict_of_ae_restrict_of_subset hsmall ((hsplit k).representative i))
    exact Measure.eqOn_open_of_ae_eq (h1.trans h2) isOpen_ball (hV k).continuous.continuousOn
      (((EuclideanSpace.proj i).continuous.comp_continuousOn (hsplit k).continuous).mono hsmall)
  let f (k : ℕ) (γ : C(Time,X)) :=
    (V k (γ t)-((1-(t:ℝ))*V k (γ 0)+(t:ℝ)*V k (γ 1)))/r k
  have hf (k : ℕ) : Measurable (f k) := by
    have hVk : Measurable (V k) := (hV k).continuous.measurable
    exact ((hVk.comp (measurable_path_eval t)).sub
      (((hVk.comp (measurable_path_eval 0)).const_mul (1-(t:ℝ))).add
        ((hVk.comp (measurable_path_eval 1)).const_mul (t:ℝ)))).div_const (r k)
  have hi (θ : Measure C(Time,X)) [IsFiniteMeasure θ] (k : ℕ) (z : Time) :
      Integrable (fun γ => V k (γ z)) θ := by
    obtain ⟨C,hC⟩ := (hVc k).exists_bound_of_continuous (hV k).continuous
    exact Integrable.of_bound
      (((hV k).continuous.measurable.comp (measurable_path_eval z)).aestronglyMeasurable)
      C (Eventually.of_forall fun γ => hC (γ z))
  have hfi (θ : Measure C(Time,X)) [IsFiniteMeasure θ] (k : ℕ) : Integrable (f k) θ :=
    ((hi θ k t).sub (((hi θ k 0).const_mul (1-(t:ℝ))).add
      ((hi θ k 1).const_mul (t:ℝ)))).div_const (r k)
  have hres (θ : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (θ k)]
      (hgθ : ∀ k, ∀ᵐ γ ∂θ k, IsGeodesic γ)
      (hoθ : ∀ k, IsOptimalCoupling ((θ k).map (fun γ => γ 0))
        ((θ k).map (fun γ => γ 1)) ((θ k).map (fun γ => (γ 0,γ 1))))
      (C : ℝ) (hC : 0 ≤ C)
      (hcθ : ∀ k (z : Time), (θ k).map (fun γ => γ z) ≤
        ENNReal.ofReal (C/m.real (ball (p k) (4*r k))) • m)
      (hs0 : ∀ k, ∀ᵐ x ∂(θ k).map (fun γ => γ 0), dist x (p k) ≤ r k/12)
      (hs1 : ∀ k, ∀ᵐ x ∂(θ k).map (fun γ => γ 1), dist x (p k) ≤ r k/12) :
      Tendsto (fun k => ∫ γ, f k γ ∂θ k) atTop (𝓝 0) := by
    have hb (k : ℕ) := optimal_geodesic_plan_bounded ((θ k).map (fun γ => γ 0))
      ((θ k).map (fun γ => γ 1)) (θ k) (hgθ k) (hoθ k) (p k)
      (by linarith [hr k] : 0 ≤ r k/12) (hs0 k) (hs1 k)
    have he (k : ℕ) (z : Time) : (∫ γ, V k (γ z) ∂θ k)=∫ γ, v k (γ z) i ∂θ k := by
      apply integral_congr_ae
      filter_upwards [hb k] with γ hγ
      exact hEq k ((hγ.2 z).trans_lt (by linarith [hr k]))
    have heint (k : ℕ) : (∫ γ, f k γ ∂θ k)=
        ((∫ γ, v k (γ t) i ∂θ k)-((1-(t:ℝ))*(∫ γ, v k (γ 0) i ∂θ k)+
          (t:ℝ)*(∫ γ, v k (γ 1) i ∂θ k)))/r k := by
      change (∫ γ, (V k (γ t)-((1-(t:ℝ))*V k (γ 0)+(t:ℝ)*V k (γ 1)))/r k ∂θ k)=_
      rw [integral_div,integral_sub (f := fun γ : C(Time,X) => V k (γ t))
        (g := fun γ : C(Time,X) => (1-(t:ℝ))*V k (γ 0)+(t:ℝ)*V k (γ 1))
        (hi (θ k) k t) (((hi (θ k) k 0).const_mul _).add ((hi (θ k) k 1).const_mul _)),
        integral_add (f := fun γ : C(Time,X) => (1-(t:ℝ))*V k (γ 0))
          (g := fun γ : C(Time,X) => (t:ℝ)*V k (γ 1))
          ((hi (θ k) k 0).const_mul _) ((hi (θ k) k 1).const_mul _)]
      simp only [integral_const_mul,he]
    simpa only [heint] using hX.first_order_affine_mean hn hK p r ε hr hr0 hcurv
      hε hε1 hε0 u v hsplit θ hgθ hoθ hC hcθ hs0 hs1 i t
  let S k := {γ | 0 ≤ f k γ}
  let κ k := halfRestrictedMeasure (π k) (S k)
  let ρ k := (κ k univ)⁻¹ • κ k
  have hdata (k : ℕ) := half_restricted_optimal_plan (π k) (hgeo k) (hopt k)
    (finite_second_moment_cost
      (finiteSecondMoment_of_bounded ((π k).map (fun γ => γ 0)) (p k) (hs₀ k))
      (finiteSecondMoment_of_bounded ((π k).map (fun γ => γ 1)) (p k) (hs₁ k))
      (hopt k).1 (hopt k).2.1)
    m (hcomp k) (p k) (hs₀ k) (hs₁ k) (S k)
  let (k : ℕ) : IsProbabilityMeasure (ρ k) := (hdata k).1
  have hcρ (k : ℕ) (z : Time) : (ρ k).map (fun γ => γ z) ≤
      ENNReal.ofReal ((2*B)/m.real (ball (p k) (4*r k))) • m := by
    rw [show (2*B)/m.real (ball (p k) (4*r k))=2*(B/m.real (ball (p k) (4*r k))) by ring,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    simpa only [ENNReal.ofReal_ofNat] using (hdata k).2.2.2.1 z
  have hlim := integral_abs_tendsto_of_halfRestrictedMeans π f hf (fun k => hfi (π k) k)
    (hres π hgeo hopt B hB hcomp hs₀ hs₁)
    (hres ρ (fun k => (hdata k).2.1) (fun k => (hdata k).2.2.1) (2*B) (by positivity) hcρ
      (fun k => (hdata k).2.2.2.2.1) (fun k => (hdata k).2.2.2.2.2))
  have hb (k : ℕ) := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
    ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
    (by linarith [hr k] : 0 ≤ r k/12) (hs₀ k) (hs₁ k)
  have he (k : ℕ) : (∫ γ, |f k γ| ∂π k)=
      (∫ γ, |v k (γ t) i-((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i)| ∂π k)/r k := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hb k] with γ hγ
    have hsame (z : Time) : V k (γ z)=v k (γ z) i :=
      hEq k ((hγ.2 z).trans_lt (by linarith [hr k]))
    simp only [f,hsame,abs_div,abs_of_pos (hr k)]
  simpa only [he] using hlim

end RegularPointCoordinates

end

end OAI
