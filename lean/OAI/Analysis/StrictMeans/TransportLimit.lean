import OAI.Analysis.StrictMeans.BoxSlope

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma integrable_jacobianPart_base (μ : ProbabilityMeasure DiskFamily) (k : ℝ) (positive : Bool) :
    Integrable (fun f => jacobianPart k f positive UpperHalfPlane.I) (μ : Measure DiskFamily) :=
  ((continuous_jacobianPart k positive).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma jacobianPart_nonneg (k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    0 ≤ jacobianPart k f positive z := le_max_right _ _

lemma lintegral_jacobianPart_base (μ : ProbabilityMeasure DiskFamily) (k : ℝ) (positive : Bool) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (∫ f, jacobianPart k f positive UpperHalfPlane.I ∂(μ : Measure DiskFamily)) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_jacobianPart_base μ k positive)
    (Eventually.of_forall (fun f => jacobianPart_nonneg k f positive _))).symm

lemma truncated_transport_le (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k N : ℝ} (hk : 0 < k)
    (hβ : 3*(k-1)=β-1) (hN : 1 ≤ N) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      transportTest k N (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  apply ennreal_box_slope (by rw [lintegral_jacobianPart_base]; exact ENNReal.ofReal_ne_top) hN
  intro S Y hS hY
  exact box_transport_expectation μ β hlaw hk hβ hN hS hY

lemma weighted_transport_le (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I)) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hm (n : ℕ) : Measurable (fun f : DiskFamily =>
      ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I)*transportTest k (n+1) (f,UpperHalfPlane.I)) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      ((measurable_transportTest hk _).comp (measurable_id.prodMk measurable_const))
  have hmono : Monotone (fun n : ℕ => fun f : DiskFamily =>
      ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I)*transportTest k (n+1) (f,UpperHalfPlane.I)) := by
    intro n m hnm f
    exact mul_le_mul' le_rfl (transportTest_nat_monotone _ hnm)
  simp_rw [← iSup_transportTest (k := k),ENNReal.mul_iSup]
  rw [lintegral_iSup hm hmono]
  apply iSup_le
  intro n
  exact truncated_transport_le μ β hlaw hk hβ (by exact_mod_cast Nat.succ_pos n)

end
end StrictInverseFirstPower

end

end OAI
