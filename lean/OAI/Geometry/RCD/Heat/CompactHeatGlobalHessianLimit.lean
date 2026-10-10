import OAI.Geometry.RCD.Heat.CompactHeatHessianTails
import OAI.Geometry.RCD.Heat.CompactHeatLocalScaledHessianLimit
import OAI.Geometry.RCD.Sobolev.CutoffIntegralLimit

namespace OAI
/-! # Global convergence of the actual scaled heat Hessian -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem global_scaled_hessian_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (u v WU WV UV : ℕ → InteriorHeatTime δ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t.val)
        (mul_pos (div_pos (hε k) (by norm_num)) t.val.property.1))
    (hv : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t.val))
        (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWU : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k t))
    (hWV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k t))
    (hUV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k t) (v k t))
    (j : ℕ → ℕ) (hj : StrictMono j) (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ I : ℝ, Tendsto (fun k => ∫ x, (ε (D.index (j k))/2)^2*
      localHessianAction m q w (u (D.index (j k)) t) (v (D.index (j k)) t)
        (WU (D.index (j k)) t) (WV (D.index (j k)) t) (UV (D.index (j k)) t) x ∂m) atTop (𝓝 I) := by
  intro m q w
  obtain ⟨L,hL,htail⟩ := D.scaled_hessian_uniform_tails hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
    hR hδ hS hT f A hf ha u v WU WV UV hu hv hWU hWV hUV
  let i k := D.index (j k)
  let F k x := (ε (i k)/2)^2*localHessianAction m q w (u (i k) t) (v (i k) t)
    (WU (i k) t) (WV (i k) t) (UV (i k) t) x
  let r (N : ℕ) := (2:ℝ)^N*L
  have hr (N : ℕ) : 0 < r N := mul_pos (by positivity) (lt_of_lt_of_le (by norm_num) hL)
  let φ N := radialCutoff p (r N)
  apply exists_integral_limit_of_cutoffs m F φ (fun N => ball p (r N))
    (fun k => (localHessianAction_integrable m q w (u (i k) t) (v (i k) t)
      (WU (i k) t) (WV (i k) t) (UV (i k) t)).const_mul _)
    (fun N => (radialCutoff_lipschitz p (hr N)).continuous.aestronglyMeasurable)
    (fun N x => radialCutoff_bounds p (r N) x)
    (fun N x hx => radialCutoff_eq_one p (hr N) (by simpa only [dist_comm] using (mem_ball.mp hx).le))
  · intro N
    have hsupport : tsupport (φ N) ⊆ closedBall p (2*r N) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn
      exact hx (radialCutoff_eq_zero p (hr N)
        (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hn)))
    obtain ⟨J,hJ⟩ := D.local_scaled_hessian_limit hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
      hR (show 0 < 2*r N by positivity) hδ hS hT t ht (φ N) _ (radialCutoff_lipschitz p (hr N))
      (radialCutoff_hasCompactSupport p (hr N)) (fun x => radialCutoff_bounds p (r N) x) hsupport
      f A hf ha j hj Q₀ hweak (fun k => u (i k) t) (fun k => v (i k) t)
      (fun k => WU (i k) t) (fun k => WV (i k) t) (fun k => UV (i k) t)
      (fun k => hu (i k) t) (fun k => hv (i k) t)
      (fun k => hWU (i k) t) (fun k => hWV (i k) t) (fun k => hUV (i k) t)
    refine ⟨_,hJ.congr' (Eventually.of_forall fun k => ?_)⟩
    calc
      _ = ∫ x, φ N x*(ε (i k)/2)^2*localHessianAction m q w (u (i k) t) (v (i k) t)
          (WU (i k) t) (WV (i k) t) (UV (i k) t) x ∂m := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : φ N x=0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hsupport hs))
        rw [hz,zero_mul,zero_mul]
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [F]; ring
  · apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [(Metric.tendstoUniformly_iff.mp htail) e he] with N hN k
    exact hN (i k,t)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
