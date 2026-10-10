import OAI.Geometry.Kahler.BaseLaterMoments

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_scale (a ε : ℝ) (v : ℂ) : regularizedLog a ε v=regularizedLog 1 ε ((a:ℂ)*v) := by
  simp only [regularizedLog,Complex.ofReal_one,one_mul]

lemma density_log_comparison {a : ℝ} (pr : RadialProfiles a) {Q M i N : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (P : ℕ → Finset Sphere)
    {ε θ : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (c : ℂ)
    (hratio : ∀ ξ : Sphere, ‖logNormalized ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ)‖ ≤ θ)
    (hposi : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P i ξ)
    (hposN : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P N ξ)
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P i))]
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))] :
    |(∫ ξ : Sphere, regularizedLog 1 ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ) ∂densityMeasure (density Q pr.R pr.f pr.b P N))-
      (∫ ξ : Sphere, regularizedLog 1 ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ) ∂densityMeasure (density Q pr.R pr.f pr.b P i))| ≤
      4*θ^(M+1)/(1-θ) := by
  let V : Sphere → ℂ := fun ξ => c*peakPolynomial (P (Q^i)) (Q^i) ξ
  have hV : Continuous V := continuous_const.mul ((peakPolynomial_analytic _ _).continuous.comp continuous_subtype_val)
  let f : Sphere → ℝ := fun ξ => regularizedLog 1 ε (V ξ)
  let g : Sphere → ℝ := fun ξ => logTruncation ε M (V ξ)
  have hf : Continuous f := (regularizedLog_contDiff 1 he).continuous.comp hV
  have hg : Continuous g := (logTruncation_continuous ε M).comp hV
  have hb : ∀ ξ, |f ξ-g ξ| ≤ 2*θ^(M+1)/(1-θ) := fun ξ => logTruncation_error he hθ hθ1 (hratio ξ) M
  have h1 := probability_integral_error (μ := densityMeasure (density Q pr.R pr.f pr.b P N))
    (compact_continuous_integrable hf) (compact_continuous_integrable hg) hb
  have h2 := probability_integral_error (μ := densityMeasure (density Q pr.R pr.f pr.b P i))
    (compact_continuous_integrable hf) (compact_continuous_integrable hg) hb
  have hW (j : ℕ) : Continuous (density Q pr.R pr.f pr.b P j) :=
    (density_smooth (by omega : 0 < Q) pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j).continuous
  have hpersist : (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P N))=
      ∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i) := by
    rw [densityMeasure_integral (hW N) hposN,densityMeasure_integral (hW i) hposi]
    simp only [smul_eq_mul]
    simpa only [mul_comm] using logTruncation_density_persist pr hQ hM hiN P ε c
  rw [hpersist] at h1
  have hh := abs_sub_le (∫ ξ, f ξ ∂densityMeasure (density Q pr.R pr.f pr.b P N))
    (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))
    (∫ ξ, f ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))
  rw [abs_sub_comm (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))] at hh
  exact hh.trans (by convert add_le_add h1 h2 using 1; ring)

lemma logarithmicTest_later_threshold {a : ℝ} (ha : 0 ≤ a) {ε : ℝ} (he : ε ≠ 0) {d : ℝ} (hd : 0 < d) :
    ∃ M : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 4*θ^(M+1)/(1-θ) ≤ d ∧
      ∀ q ∈ Icc 0 (a*gaussianConstant), q/logFactor q ε ≤ θ := by
  obtain ⟨θ,hθ,hθ1,hb⟩ := logFactor_ratio_bound he (mul_nonneg ha gaussianConstant_pos.le)
  have ht : Tendsto (fun M : ℕ => 4*θ^(M+1)/(1-θ)) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const θ
    simpa only [← pow_succ,mul_zero,zero_mul,zero_div] using (hh.const_mul 4).div_const (1-θ)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hd))
  exact ⟨M,θ,hθ,hθ1,(hM M le_rfl).le,hb⟩

end PinchedHartogs.BaseConstruction

end

end OAI
