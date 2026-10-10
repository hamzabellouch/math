import OAI.Geometry.RCD.Harmonic.ControlledCoefficientPathSelection
import OAI.Geometry.RCD.Harmonic.FirstOrderUniformAffineMean

namespace OAI

/-! # Controlled coefficient paths for the original first-order coordinates -/

open Set Filter MeasureTheory Metric Finset
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_coefficient_paths {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) ((π k).map (fun γ => (γ 0,γ 1))))
    {B : ℝ} (hB : 0≤B)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤
      ENNReal.ofReal (B/(hausdorff n X).real (ball (p k) (4*r k))) • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k)≤r k/12)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k)≤r k/12)
    (G : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    {M : ℝ} (henergy : ∀ k, (r k)^2*
      (∑ i, ∫ x in ball (p k) (r k), localGamma (hausdorff n X) hX.quadratic (G k i) (G k i) x
        ∂hausdorff n X)≤M*(hausdorff n X).real (ball (p k) (4*r k)))
    (E : ℕ → X → ℝ) (hE : ∀ k x, 0≤E k x)
    (hEI : ∀ k, IntegrableOn (E k) (ball (p k) (r k)) (hausdorff n X))
    (hE0 : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (4*r k)))⁻¹*
      ∫ x in ball (p k) (r k), E k x ∂hausdorff n X) atTop (𝓝 0))
    (P : ℕ → C(Time,X) → Prop) (hP : ∀ k, ∀ᵐ γ ∂π k, P k γ) :
    ∃ (γ : ℕ → C(Time,X)) (b : ℕ → Fin n → ℝ → ℝ) (a : ℕ → ℝ),
      (∀ k, P k (γ k)) ∧ (∀ k, IsGeodesic (γ k)) ∧
      (∀ k (t : Time), dist (γ k t) (p k)≤r k/4) ∧
      (∀ k, 0≤a k) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ k i (t : Time),
        |(v k (γ k t) i-((1-(t:ℝ))*v k (γ k 0) i+(t:ℝ)*v k (γ k 1) i))/r k|≤a k) ∧
      (∀ k i, AbsolutelyContinuousOnInterval (b k i) 0 1) ∧
      (∀ k i, b k i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
        fun t => SobolevSpace.toLp (hausdorff n X) hX.quadratic (G k i) (geodesicExtension (γ k) t)) ∧
      Tendsto (fun k => ∫ t in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) t)) atTop (𝓝 0) ∧
      Tendsto (fun k => a k*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b k i) t|)) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hm (k : ℕ) : 0<μ.real (ball (p k) (4*r k)) := ENNReal.toReal_pos
    (hX.fullSupport _ _ (by linarith [hr k])).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  let C k := ENNReal.ofReal (B/μ.real (ball (p k) (4*r k)))
  have hbounded (k : ℕ) := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
    ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
    (show 0≤r k/12 by linarith [hr k]) (hs₀ k) (hs₁ k)
  have hstay (k : ℕ) (t : Time) : ∀ᵐ x ∂(π k).map (fun γ => γ t), x∈ball (p k) (r k) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [hbounded k] with γ hγ
    exact (hγ.2 t).trans_lt (by linarith [hr k])
  have hspeed (k : ℕ) : ∀ᵐ γ ∂π k, dist (γ 0) (γ 1)≤r k := by
    filter_upwards [hbounded k] with γ hγ
    have hh := dist_triangle (γ 0) (p k) (γ 1)
    rw [dist_comm (p k) (γ 1)] at hh
    linarith [hγ.2 0,hγ.2 1,hr k]
  have hD (k : ℕ) : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (π k) := by
    apply MemLp.of_bound ((continuous_eval_const 0).dist (continuous_eval_const 1)).aestronglyMeasurable (r k)
    filter_upwards [hspeed k] with γ hγ
    simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hγ
  choose F hFc hFeq hFI hF0 using fun i =>
    hX.first_order_uniform_affine_mean hn hK p r ε hr hr0 hcurv hε hε1 hε0 u v hsplit
      π hgeo hopt hB hcomp hs₀ hs₁ i
  have hFsum : Tendsto (fun k => ∫ γ, ∑ i, ‖F i k γ‖ ∂π k) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum univ (fun i _ => hF0 i)
    simpa only [integral_finsetSum _ (fun i _ => hFI i _),sum_const_zero] using hh
  have hI (k : ℕ) := compressed_segment_integral μ (π k) ENNReal.ofReal_ne_top (hcomp k) (hstay k)
    (hEI k) (Eventually.of_forall (hE k))
  have hEplan : Tendsto (fun k => ∫ γ, (∫ t in Icc (0:ℝ) 1,
      E k (geodesicExtension γ t)) ∂π k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun γ => integral_nonneg (fun _ => hE k _)))
      (g := fun k => B*(μ.real (ball (p k) (4*r k)))⁻¹*
        ∫ x in ball (p k) (r k), E k x ∂μ)
    · intro k
      have hh := (hI k).2.2
      rw [ENNReal.toReal_ofReal (div_nonneg hB (hm k).le)] at hh
      convert hh using 1
      ring
    · simpa only [mul_zero,mul_assoc] using hE0.const_mul B
  have hGbound (k : ℕ) : (n:ℝ)*(r k)^2*(C k).toReal*
      (∑ i, ∫ x in ball (p k) (r k), localGamma μ Q (G k i) (G k i) x ∂μ)≤(n:ℝ)*B*M := by
    rw [show (C k).toReal=B/μ.real (ball (p k) (4*r k)) from ENNReal.toReal_ofReal (div_nonneg hB (hm k).le)]
    calc
      _ = ((n:ℝ)*B/μ.real (ball (p k) (4*r k)))*((r k)^2*
          (∑ i, ∫ x in ball (p k) (r k), localGamma μ Q (G k i) (G k i) x ∂μ)) := by ring
      _ ≤ ((n:ℝ)*B/μ.real (ball (p k) (4*r k)))*(M*μ.real (ball (p k) (4*r k))) :=
        mul_le_mul_of_nonneg_left (henergy k) (by positivity)
      _ = _ := by field_simp [(hm k).ne']
  let R k γ := P k γ ∧ (IsGeodesic γ ∧ ∀ t : Time, dist (γ t) (p k)≤r k/4) ∧
    ∀ i (t : Time), F i k γ t=
      (v k (γ t) i-((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i))/r k
  have hR (k : ℕ) : ∀ᵐ γ ∂π k, R k γ := by
    filter_upwards [hP k,hbounded k,ae_all_iff.mpr (fun i => hFeq i k)] with γ hp hb he
    exact ⟨hp,⟨hb.1,fun t => by linarith [hb.2 t]⟩,he⟩
  obtain ⟨γ,b,hRγ,hb,he,hAlim,hZlim,hprod⟩ := controlled_coefficient_path_selection μ Q G π
    hgeo C (fun _ => ENNReal.ofReal_ne_top) hcomp hD r hspeed
    (fun k => ball (p k) (r k)) hstay hGbound (fun k i => F i k)
    (fun k i => hFI i k) hFsum E hE hEI hEplan R hR
  refine ⟨γ,b,fun k => ∑ i, ‖F i k (γ k)‖,fun k => (hRγ k).1,fun k => (hRγ k).2.1.1,
    fun k => (hRγ k).2.1.2,fun k => sum_nonneg (fun _ _ => norm_nonneg _),hAlim,?_,hb,he,hZlim,hprod⟩
  intro k i t
  rw [← (hRγ k).2.2 i t]
  exact ((F i k (γ k)).norm_coe_le_norm t).trans
    (single_le_sum (fun j _ => norm_nonneg (F j k (γ k))) (mem_univ i))

end RegularPointCoordinates

end

end OAI
