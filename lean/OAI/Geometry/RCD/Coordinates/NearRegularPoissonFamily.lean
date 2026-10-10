import OAI.Geometry.RCD.Coordinates.NearRegularDistanceSources
import OAI.Geometry.RCD.Sobolev.DistancePoissonFamily
import OAI.Geometry.RCD.Metric.AnnularVolume

namespace OAI

/-! # Constructed Poisson families along every near-regular shrinking sequence

One finite initial segment is discarded. Thereafter the actual positive
sources have vanishing relative mass and the replacement constants are fixed.
-/

open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.near_regular_poisson_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (hK : K≤0) {o : X} (ho : IsRegular n o)
    (p : ℕ → X) (r : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 o))
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ B J C : ℝ, 0<B ∧ 0<J ∧ 1≤C ∧ ∃ N : ℕ,
      ∃ F : DistancePoissonFamily (hausdorff n X) hX.quadratic n (-K) B J C
        (fun k => p (k+N)) (fun k => r (k+N)) (fun k => hr (k+N)),
        (∀ k, r (k+N)≤1 ∧ -1≤K*(64*r (k+N))^2 ∧
          0<(hausdorff n X).real (ball (p (k+N)) (r (k+N))) ∧
          2*(hausdorff n X).real (ball (p (k+N)) (r (k+N)))≤
            (hausdorff n X).real (ball (p (k+N)) (2*r (k+N)))) ∧
        Tendsto (fun k => (r (k+N))^(-(n:ℝ))*(F.source k).real (ball (p (k+N)) (r (k+N))))
          atTop (𝓝 0) ∧
        Tendsto (fun k => (F.source k).real (ball (p (k+N)) (r (k+N)))/
          (hausdorff n X).real (ball (p (k+N)) (r (k+N)))) atTop (𝓝 0) ∧
        Tendsto (fun k => ‖normalizeLocalL2 (hausdorff n X) (ball (p (k+N)) (r (k+N)))
          (hX.finiteOnBounded _ isBounded_ball).ne
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p (k+N)) (r (k+N)))
            (((r (k+N))^2)⁻¹ • (F.datum k-F.replacement k)))‖) atTop (𝓝 0) := by
  let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  dsimp only
  obtain ⟨σ,hσ,heik,hsource,hmass⟩ := hX.regular_moving_distance_sources hn hK ho p r hp hr hr0
  obtain ⟨B,J,C,hB,hJ,hC,hsolve⟩ := hX.uniform_distance_poisson_replacement hn (neg_nonneg.mpr hK)
  let ω := euclideanUnitVolume n
  have hω : 0<ω := euclideanUnitVolume_pos n
  have hv := hX.regular_moving_volume_limit hn ho p r hp hr hr0
  have ht : Tendsto (fun k => 2*r k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr0.const_mul 2
  have hw := hX.regular_moving_volume_limit hn ho p (fun k => 2*r k) hp
    (fun k => mul_pos (by norm_num) (hr k)) ht
  have hvr : Tendsto (fun k => (hausdorff n X).real (ball (p k) (r k))/(ω*(r k)^n))
      atTop (𝓝 1) := by
    convert hv.div_const ω using 1
    · funext k
      ring
    · simp only [ω,div_self hω.ne']
  have hwr : Tendsto (fun k => (hausdorff n X).real (ball (p k) (2*r k))/(ω*(2*r k)^n))
      atTop (𝓝 1) := by
    convert hw.div_const ω using 1
    · funext k
      ring
    · simp only [ω,div_self hω.ne']
  have hvsmall : ∀ᶠ k in atTop,
      |(hausdorff n X).real (ball (p k) (r k))/(ω*(r k)^n)-1|<1/4 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hvr.eventually (ball_mem_nhds 1 (by norm_num : (0:ℝ)<1/4))
  have hwsmall : ∀ᶠ k in atTop,
      |(hausdorff n X).real (ball (p k) (2*r k))/(ω*(2*r k)^n)-1|<1/4 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hwr.eventually (ball_mem_nhds 1 (by norm_num : (0:ℝ)<1/4))
  have hcurv0 : Tendsto (fun k => K*(64*r k)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : 2≠0)] using ((hr0.const_mul 64).pow 2).const_mul K
  have hc : ∀ᶠ k in atTop, -1<K*(64*r k)^2 :=
    hcurv0.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0))
  have hr1 : ∀ᶠ k in atTop, r k<1 := hr0.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (((hr1.and hc).and hvsmall).and hwsmall)
  have hgood k : r (k+N)≤1 ∧ -1≤K*(64*r (k+N))^2 ∧
      0<(hausdorff n X).real (ball (p (k+N)) (r (k+N))) ∧
      2*(hausdorff n X).real (ball (p (k+N)) (r (k+N)))≤
        (hausdorff n X).real (ball (p (k+N)) (2*r (k+N))) := by
    have hh := hN (k+N) (Nat.le_add_left N k)
    exact ⟨hh.1.1.1.le,hh.1.1.2.le,
      relative_volume_annulus hn (hr (k+N)) hω hh.1.2.le hh.2.le⟩
  have hex k := hsolve (p (k+N)) (r (k+N)) (hr (k+N))
    (hgood k).1 (hgood k).2.1 (hgood k).2.2.1 (hgood k).2.2.2
    (σ (k+N)) (hσ (k+N)) (heik (k+N)) (hsource (k+N) C)
  choose χ f hf hlap hheight _hgrad henergy hdensity using hex
  let F : DistancePoissonFamily (hausdorff n X) hX.quadratic n (-K) B J C
      (fun k => p (k+N)) (fun k => r (k+N)) (fun k => hr (k+N)) := {
    source := fun k => σ (k+N)
    finite := fun k => hσ (k+N)
    cutoff := χ
    replacement := f
    eikonal := fun k => heik (k+N)
    defect := fun k => hsource (k+N) C (χ k)
    boundary := hf
    laplacian := hlap
    height := hheight
    energy_error := henergy
    density_error := hdensity }
  refine ⟨B,J,C,hB,hJ,hC,N,F,hgood,?_,?_⟩
  · exact hmass.comp (tendsto_add_atTop_nat N)
  · have hnum : Tendsto (fun k => (σ k).real (ball (p k) (r k))/(r k)^n) atTop (𝓝 0) := by
      convert hmass using 1
      funext k
      rw [Real.rpow_neg (hr k).le,Real.rpow_natCast,div_eq_inv_mul]
    have hquot := hnum.div hv hω.ne'
    have heq : (fun k => (σ k).real (ball (p k) (r k))/(hausdorff n X).real (ball (p k) (r k))) =ᶠ[atTop]
        fun k => ((σ k).real (ball (p k) (r k))/(r k)^n)/
          ((hausdorff n X).real (ball (p k) (r k))/(r k)^n) := by
      exact Eventually.of_forall fun k => by field_simp [(pow_pos (hr k) n).ne']
    have hratio := (hquot.congr' heq.symm).comp (tendsto_add_atTop_nat N)
    have hrF : Tendsto (fun k => (F.source k).real (ball (p (k+N)) (r (k+N)))/
        (hausdorff n X).real (ball (p (k+N)) (r (k+N)))) atTop (𝓝 0) := by
      simpa only [zero_div,Function.comp_def,F] using hratio
    refine ⟨hrF,?_⟩
    exact F.normalized_value_error_tendsto_zero (annularPoincareConstant_pos K n).le
      (fun k => (hgood k).2.2.1)
      (fun k => hX.annular_dirichlet_poincare hn (p (k+N)) (hr (k+N))
        (hgood k).1 (hgood k).2.2.1 (hgood k).2.2.2) hrF

end RegularPointCoordinates

end

end OAI
