import OAI.Geometry.RCD.Sobolev.CutoffBochnerConvergence
import OAI.Geometry.RCD.Sobolev.CompactLaplacian

namespace OAI

/-! # Vanishing full Bochner mass near a harmonic constant-energy limit -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem GoodLaplacianCutoff.harmonic_limit_terms_zero
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hb : 2*r < b) (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma μ Q u u =ᵐ[μ.restrict (ball p b)] fun _ => c) :
    (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u+
      (∫ x, χ.weight x*(d x)^2 ∂μ)+weightedGamma μ Q d u χ.sobolev = 0 := by
  have hout (x : X) (hx : x ∉ ball p b) : 2*r < dist p x := by
    have hh : b ≤ dist p x := by simpa only [mem_ball,dist_comm,not_lt] using hx
    exact hb.trans_le hh
  have hqzero : ∫ x, χ.laplacian x ∂μ = 0 :=
    integral_weakLaplacian_eq_zero μ Q χ.sobolev χ.laplacian χ.weak_laplacian p
      (show 0 < 2*r by positivity)
      (by
        filter_upwards [χ.representative] with x hx hdist
        exact hx.trans (χ.zero x hdist))
      (by
        filter_upwards [χ.laplacian_locality] with x hx hdist
        exact hx (Or.inr hdist))
  have hq : weightedGamma μ Q χ.laplacian u u=0 := by
    have he : (fun x => χ.laplacian x*localGamma μ Q u u x) =ᵐ[μ]
        fun x => χ.laplacian x*c := by
      filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hc,χ.laplacian_locality]
        with x hx hloc
      by_cases hm : x∈ball p b
      · rw [hx hm]
      · rw [hloc (Or.inr (hout x hm)),zero_mul,zero_mul]
    change (∫ x, χ.laplacian x*localGamma μ Q u u x ∂μ)=0
    rw [integral_congr_ae he,integral_mul_const,hqzero,zero_mul]
  have hsquare : (∫ x, χ.weight x*(d x)^2 ∂μ)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd] with x hx
    change χ.weight x*(d x)^2 = (0:ℝ)
    by_cases hm : x∈ball p b
    · simp only [hx hm,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
    · rw [χ.zero x (hout x hm),zero_mul]
  have hcross : weightedGamma μ Q d u χ.sobolev=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd,χ.representative,
      localGamma_comm μ Q u χ.sobolev,localGamma_zero_on_level μ Q χ.sobolev u 0]
        with x hx hrep hcomm hlevel
    change d x*localGamma μ Q u χ.sobolev x = (0:ℝ)
    by_cases hm : x∈ball p b
    · rw [hx hm,zero_mul]
    · rw [hcomm,hlevel (hrep.trans (χ.zero x (hout x hm))),mul_zero]
  rw [hq,hsquare,hcross]
  ring

theorem GoodLaplacianCutoff.bochner_source_tendsto_zero
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hC : 0 ≤ C) (hb : 2*r < b)
    (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma μ Q u u =ᵐ[μ.restrict (ball p b)] fun _ => c)
    (us ds Gs : ℕ → SobolevSpace μ Q)
    (hds : ∀ k, IsWeakLaplacian μ Q (us k) (SobolevSpace.toLp μ Q (ds k)))
    (hGs : ∀ k, SobolevSpace.toLp μ Q (Gs k) =ᵐ[μ] localGamma μ Q (us k) (us k))
    (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u))
    (hdconv : Tendsto (fun k => SobolevSpace.toLp μ Q (ds k)) atTop (𝓝 d)) :
    Tendsto (fun k => -(1/2:ℝ)*energyForm μ Q (Gs k) χ.sobolev-
        weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) (us k) (ds k)) atTop (𝓝 0) := by
  have hh := χ.bochner_source_tendsto μ Q hC u d us ds Gs hds hGs L hus hu hconv hdconv
  rwa [χ.harmonic_limit_terms_zero μ Q hr hb u d hd c hc] at hh

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.measure_mass_tendsto_zero
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)]
    (hlim : Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop (𝓝 0))
    {S : Set X} (hS : MeasurableSet S) (hSone : ∀ x∈S, χ.weight x=1) :
    Tendsto (fun k => (σ k).real S) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => measureReal_nonneg) _ hlim
  intro k
  have hb : S.indicator (fun _ => (1:ℝ)) ≤ᵐ[σ k] χ.weight := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S
    · rw [indicator_of_mem hx,hSone x hx]
    · simpa only [indicator_of_notMem hx] using (χ.bounds x).1
  have hh := integral_mono_ae ((integrable_const (1:ℝ)).indicator hS)
    (χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)) hb
  simpa only [integral_indicator hS,setIntegral_const,smul_eq_mul,mul_one] using hh

end RegularPointCoordinates

end

end OAI
