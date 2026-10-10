import OAI.Geometry.RCD.Sobolev.LocalSourceStrongGradient
import OAI.Geometry.RCD.Sobolev.RadialLocalSobolevLimit

namespace OAI

/-! # Strong local gradients for the canonical radial Sobolev realizations -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem radial_source_strong_gradient (z : X) {r : ℝ} (hr : 0 < r)
    (F : ℕ → X → ℝ) (f : X → ℝ) (L A : ℝ≥0)
    (hF : ∀ k, LipschitzOnWith L (F k) (closedBall z (2*r)))
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hFb : ∀ k, ∀ x ∈ closedBall z (2*r), |F k x| ≤ A)
    (hfb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A)
    (hc : TendstoUniformly (fun k (x : closedBall z (2*r)) => F k x) (fun x => f x) atTop)
    (φ : X → ℝ) {Lφ B : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hB : ∀ x, |φ x| ≤ B) (hφ0 : ∀ x, 0 ≤ φ x)
    (hzero : ∀ x ∉ closedBall z r, φ x = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ k, ∃ (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ),
      IsWeakLaplacian μ Q u d ∧
      (SobolevSpace.toLp μ Q u =ᵐ[μ.restrict (closedBall z r)] F k) ∧
      Integrable (fun x => φ x*|d x|) μ ∧ (∫ x, φ x*|d x| ∂μ) ≤ C) :
    Tendsto (fun k => weightedGamma μ Q (fun x => (φ x)^2)
      (radialLocalSobolev μ Q z hr (hF k) (hFb k)-radialLocalSobolev μ Q z hr hf hfb)
      (radialLocalSobolev μ Q z hr (hF k) (hFb k)-radialLocalSobolev μ Q z hr hf hfb))
      atTop (𝓝 0) := by
  choose u d hd hu hdi hdC using hsource
  let η := SobolevSpace.ofLipschitzCompact μ Q hφ hs
  have hη : SobolevSpace.toLp μ Q η =ᵐ[μ] φ := SobolevSpace.ofLipschitzCompact_coe μ Q hφ hs
  have hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ Q η x| ≤ Lφ := by
    filter_upwards [SobolevSpace.minimalSlope_le_lipschitz μ Q η hφ hη,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q η)] with x hx hn
    rw [abs_of_nonneg hn]
    exact hx
  have hsq (k : ℕ) : Integrable (fun x => (φ x)^2*|d k x|) μ := by
    have hi := (hdi k).bdd_mul hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
    apply hi.congr
    exact Eventually.of_forall fun x => by change φ x*(φ x*|d k x|)=(φ x)^2*|d k x|; ring
  have hmass (k : ℕ) : (∫ x, (φ x)^2*|d k x| ∂μ) ≤ (B:ℝ)*C := by
    calc
      _ ≤ ∫ x, (B:ℝ)*(φ x*|d k x|) ∂μ := by
        apply integral_mono_ae (hsq k) ((hdi k).const_mul B)
        exact Eventually.of_forall fun x => by
          have hbφ := (le_abs_self (φ x)).trans (hB x)
          nlinarith [mul_nonneg (hφ0 x) (abs_nonneg (d k x)),
            mul_nonneg (sub_nonneg.mpr hbφ) (mul_nonneg (hφ0 x) (abs_nonneg (d k x)))]
      _ = (B:ℝ)*(∫ x, φ x*|d k x| ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdC k) B.coe_nonneg
  apply local_source_strong_gradient μ Q u
    (fun k => radialLocalSobolev μ Q z hr (hF k) (hFb k))
    (radialLocalSobolev μ Q z hr hf hfb) η d hd measurableSet_closedBall
  · intro k
    exact (hu k).trans (radialLocalSobolev_eq_on_ball μ Q z hr (hF k) (hFb k)).symm
  · exact radialLocalSobolev_weak_limit μ Q z hr F f L A hF hf hFb hfb
      (fun x hx => hc.tendsto_at ⟨x,hx⟩)
  · exact hφ
  · exact hs
  · exact hB
  · exact hφ0
  · exact hzero
  · exact hη
  · exact hgrad
  · exact mul_nonneg B.coe_nonneg hC
  · exact hsq
  · exact hmass
  · intro D hD
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp hc) (D/2) (by positivity))
    refine ⟨N,fun i hi j hj => ?_⟩
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (hu i),
      (ae_restrict_iff' measurableSet_closedBall).mp (hu j)] with x hix hjx hne
    have hxr : x ∈ closedBall z r := by
      by_contra hx
      exact hne (hzero x hx)
    have hx2 : x ∈ closedBall z (2*r) := closedBall_subset_closedBall (by linarith) hxr
    rw [hix hxr,hjx hxr]
    have hai := hN i hi ⟨x,hx2⟩
    have haj := hN j hj ⟨x,hx2⟩
    change dist (f x) (F i x) < D/2 at hai
    change dist (f x) (F j x) < D/2 at haj
    rw [dist_comm] at hai haj
    have htri := dist_triangle (F i x) (f x) (F j x)
    rw [dist_comm (f x) (F j x)] at htri
    simpa only [Real.dist_eq] using htri.trans (le_of_lt (by linarith))

end RegularPointCoordinates

end

end OAI
