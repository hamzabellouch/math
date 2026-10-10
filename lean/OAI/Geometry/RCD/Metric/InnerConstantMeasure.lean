import OAI.Geometry.RCD.Metric.ConstantDensityMeasure
import OAI.Geometry.RCD.Sobolev.WeakPhysicalBallTests

namespace OAI

/-! # Exact inner-ball normalization of a locally constant weak limit -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem inner_constant_measure {n : ℕ} (μ : Measure (Euclidean n)) {S ρ c : ℝ}
    (hρS : ρ ≤ S) (he : μ.restrict (ball 0 S)=ENNReal.ofReal c • volume.restrict (ball 0 S)) :
    μ.restrict (ball 0 ρ)=ENNReal.ofReal c • volume.restrict (ball 0 ρ) := by
  calc
    μ.restrict (ball 0 ρ) = (μ.restrict (ball 0 S)).restrict (ball 0 ρ) :=
      (Measure.restrict_restrict_of_subset (ball_subset_ball hρS)).symm
    _ = (ENNReal.ofReal c • volume.restrict (ball 0 S)).restrict (ball 0 ρ) := by rw [he]
    _ = ENNReal.ofReal c • volume.restrict (ball 0 ρ) := by
      rw [Measure.restrict_smul,Measure.restrict_restrict_of_subset (ball_subset_ball hρS)]

theorem inner_constant_sphere_null {n : ℕ} (μ : Measure (Euclidean n)) {S ρ c : ℝ}
    (hρ : 0 < ρ) (hρS : ρ < S)
    (he : μ.restrict (ball 0 S)=ENNReal.ofReal c • volume.restrict (ball 0 S)) :
    μ (sphere 0 ρ)=0 := by
  have hs : sphere (0 : Euclidean n) ρ ⊆ ball 0 S := by
    intro x hx
    exact (mem_sphere.mp hx).trans_lt hρS
  have hm := congrArg (fun ν : Measure (Euclidean n) => ν (sphere 0 ρ)) he
  have hv : volume (sphere (0 : Euclidean n) ρ)=0 :=
    Measure.addHaar_sphere_of_ne_zero volume 0 hρ.ne'
  simpa only [Measure.restrict_apply isClosed_sphere.measurableSet,
    inter_eq_left.mpr hs,Measure.smul_apply,smul_eq_mul,
    hv,mul_zero] using hm

private theorem cancel_inner_mass {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    (a⁻¹*b)/(a⁻¹*c)=c⁻¹*b := by
  rw [div_eq_mul_inv,mul_inv_rev,inv_inv]
  calc a⁻¹*b*(c⁻¹*a) = (a⁻¹*a)*(c⁻¹*b) := by ring
       _ = c⁻¹*b := by rw [inv_mul_cancel₀ ha,one_mul]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem inner_ball_constant_limit_test {n : ℕ} {S ρ c : ℝ}
    (hρ : 0 < ρ) (hρS : ρ < S) (hc : 0 < c)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hr : ∀ k, 0 < r k)
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hvm : ∀ k, Measurable (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k)) ≠ ⊤)
    (hpos : ∀ k, 0 < μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0))
    {Q : ProbabilityMeasure (Euclidean n)}
    (hweak : Tendsto (fun k => normalizedBallPushforward μ (p k) (r k) S (v k) (hfin k))
      atTop (𝓝 Q))
    (he : (Q : Measure (Euclidean n)).restrict (ball 0 S)=
      ENNReal.ofReal c • volume.restrict (ball 0 S)) (φ : Euclidean n →ᵇ ℝ) :
    Tendsto (fun k => (μ.real (ball (p k) (ρ*r k)))⁻¹ *
      ∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) ρ))⁻¹ * ∫ z in ball 0 ρ, φ z)) := by
  have hS := hρ.trans hρS
  have hn := inner_constant_sphere_null (Q : Measure (Euclidean n)) hρ hρS he
  have ht := physical_ball_weak_test_tendsto hS hρ hρS.le hr hv hvm hfin hpos hε hweak hn φ
  have hm := physical_ball_weak_test_tendsto hS hρ hρS.le hr hv hvm hfin hpos hε hweak hn
    (1 : Euclidean n →ᵇ ℝ)
  have heρ := inner_constant_measure (Q : Measure (Euclidean n)) hρS.le he
  have hi (ψ : Euclidean n →ᵇ ℝ) : (∫ z in ball 0 ρ, ψ z ∂(Q : Measure (Euclidean n)))=
      c * ∫ z in ball 0 ρ, ψ z := by
    rw [heρ,integral_smul_measure,ENNReal.toReal_ofReal hc.le,smul_eq_mul]
  rw [hi] at ht
  change Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹ *
    ∫ _ in ball (p k) (ρ*r k), (1:ℝ) ∂μ) atTop
    (𝓝 (∫ _ in ball (0 : Euclidean n) ρ, (1:ℝ) ∂(Q : Measure (Euclidean n)))) at hm
  change Tendsto _ _ (𝓝 (∫ z in ball 0 ρ, (1 : Euclidean n →ᵇ ℝ) z
    ∂(Q : Measure (Euclidean n)))) at hm
  rw [hi] at hm
  change Tendsto _ _ (𝓝 (c * ∫ _ in ball (0 : Euclidean n) ρ, (1:ℝ))) at hm
  simp only [setIntegral_const,smul_eq_mul,mul_one] at hm
  have hvol : 0 < volume.real (ball (0 : Euclidean n) ρ) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hρ).ne' measure_ball_ne_top
  have hq := ht.div hm (mul_pos hc hvol).ne'
  have hcanc : (c*(∫ z in ball 0 ρ, φ z))/(c*volume.real (ball (0 : Euclidean n) ρ))=
      (volume.real (ball (0 : Euclidean n) ρ))⁻¹ * ∫ z in ball 0 ρ, φ z := by
    field_simp
  rw [hcanc] at hq
  exact hq.congr' (Eventually.of_forall fun k => cancel_inner_mass (hpos k).ne' _ _)

end RegularPointCoordinates

end

end OAI
