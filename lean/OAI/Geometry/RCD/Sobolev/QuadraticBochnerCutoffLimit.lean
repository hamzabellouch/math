import OAI.Geometry.RCD.Sobolev.CutoffBochnerConvergence

namespace OAI

/-! # The exact cutoff Bochner limit for a quadratic potential -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.quadratic_limit_terms
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hb : 2*r < b) (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hu : IsWeakLaplacian μ Q u d) (n : ℝ)
    (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => n)
    (he : localGamma μ Q u u =ᵐ[μ.restrict (ball p b)]
      fun x => 2*SobolevSpace.toLp μ Q u x) :
    (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u+
      (∫ x, χ.weight x*(d x)^2 ∂μ)+weightedGamma μ Q d u χ.sobolev =
        n*(∫ x, χ.weight x ∂μ) := by
  have hout (x : X) (hx : x ∉ ball p b) : 2*r < dist p x := by
    have hh : b ≤ dist p x := by simpa only [mem_ball,dist_comm,not_lt] using hx
    exact hb.trans_le hh
  have hi : inner ℝ d (SobolevSpace.toLp μ Q χ.sobolev)=n*(∫ x, χ.weight x ∂μ) := by
    rw [L2.inner_def,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd,χ.representative] with x hx hχ
    simp only [Real.inner_apply,hχ]
    by_cases hm : x∈ball p b
    · rw [hx hm]
    · rw [χ.zero x (hout x hm)]
      ring
  have henergy : energyForm μ Q u χ.sobolev= -n*(∫ x, χ.weight x ∂μ) := by
    rw [hu,hi]
    ring
  have hfirst : weightedGamma μ Q χ.laplacian u u = -2*energyForm μ Q u χ.sobolev := by
    have hprod : (fun x => χ.laplacian x*localGamma μ Q u u x) =ᵐ[μ]
        fun x => 2*(χ.laplacian x*SobolevSpace.toLp μ Q u x) := by
      filter_upwards [(ae_restrict_iff' measurableSet_ball).mp he,χ.laplacian_locality] with x hx hloc
      by_cases hm : x∈ball p b
      · rw [hx hm]
        ring
      · rw [hloc (Or.inr (hout x hm))]
        ring
    change (∫ x, χ.laplacian x*localGamma μ Q u u x ∂μ)=_
    rw [integral_congr_ae hprod,integral_const_mul,energyForm_comm,χ.weak_laplacian,L2.inner_def]
    simp only [Real.inner_apply]
    ring
  have hsquare : (∫ x, χ.weight x*(d x)^2 ∂μ)=n^2*(∫ x, χ.weight x ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd] with x hx
    by_cases hm : x∈ball p b
    · rw [hx hm]
      ring
    · rw [χ.zero x (hout x hm)]
      ring
  have hcross : weightedGamma μ Q d u χ.sobolev=n*energyForm μ Q u χ.sobolev := by
    rw [← integral_localGamma_eq_energyForm,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd,χ.representative,
      localGamma_comm μ Q u χ.sobolev,localGamma_zero_on_level μ Q χ.sobolev u 0]
      with x hx hχ hcomm hlevel
    change d x*localGamma μ Q u χ.sobolev x=n*localGamma μ Q u χ.sobolev x
    by_cases hm : x∈ball p b
    · rw [hx hm]
    · rw [hcomm,hlevel (hχ.trans (χ.zero x (hout x hm)))]
      ring
  rw [hfirst,hsquare,hcross,henergy]
  ring

theorem GoodLaplacianCutoff.quadratic_bochner_source_tendsto
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hC : 0 ≤ C) (hb : 2*r < b)
    (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ) (hu : IsWeakLaplacian μ Q u d) (n : ℝ)
    (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => n)
    (he : localGamma μ Q u u =ᵐ[μ.restrict (ball p b)]
      fun x => 2*SobolevSpace.toLp μ Q u x)
    (us ds Gs : ℕ → SobolevSpace μ Q)
    (hds : ∀ k, IsWeakLaplacian μ Q (us k) (SobolevSpace.toLp μ Q (ds k)))
    (hGs : ∀ k, SobolevSpace.toLp μ Q (Gs k) =ᵐ[μ] localGamma μ Q (us k) (us k))
    (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q (us k) x ≤ L)
    (huL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u))
    (hdconv : Tendsto (fun k => SobolevSpace.toLp μ Q (ds k)) atTop (𝓝 d)) :
    Tendsto (fun k => -(1/2:ℝ)*energyForm μ Q (Gs k) χ.sobolev-
        weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) (us k) (ds k)) atTop
      (𝓝 (n*(∫ x, χ.weight x ∂μ))) := by
  have hlim := χ.bochner_source_tendsto μ Q hC u d us ds Gs hds hGs L hus huL hconv hdconv
  rwa [χ.quadratic_limit_terms μ Q hb u d hu n hd he] at hlim

end RegularPointCoordinates

end

end OAI
