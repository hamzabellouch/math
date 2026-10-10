import OAI.MeasureTheory.SelfSimilar.RadialLimit

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology
namespace EntropyRateDimension.BallRatios
open MeasureTheory Metric Set Filter
open scoped Topology

theorem radial_limit_of_integer (μ : Measure ℝ) [IsProbabilityMeasure μ] {x d : ℝ}
    (hx : x ∈ μ.support)
    (hlim : Tendsto (fun n : ℕ => information μ x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 d)) :
    Tendsto (fun r => information μ x r / -Real.log r) (𝓝[>] 0) (𝓝 d) := by
  let F : ℝ → ℝ := fun s => information μ x (Real.exp (-s))
  have hF : Monotone F := fun a b hab => information_antitone μ hx (Real.exp_pos _)
    (Real.exp_le_exp.mpr (neg_le_neg hab))
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF Nat.mono_cast (by simp)
    (C := 1) (fun n => by push_cast; exact le_rfl) tendsto_natCast_atTop_atTop hlim
  apply (hfull.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

end EntropyRateDimension.BallRatios

namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem ae_radial_limit (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun r => BallRatios.information (law S) x r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  filter_upwards [ae_radial_sequence S,(law S).support_mem_ae] with x hlim hx
  exact BallRatios.radial_limit_of_integer _ hx hlim

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureEntropy
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem selfSimilar_radial (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 (Coding.exponent S)) := by
  have he := S.selfSimilar_unique μ (Coding.law S) hμ (Coding.law_selfSimilar S)
  subst μ
  exact Coding.ae_radial_limit S

theorem selfSimilar_dimension (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (Coding.exponent S) :=
  LocalMass.lower_dim_eq_of_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) (S.selfSimilar_radial μ hμ)

theorem selfSimilar_entropy_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {D : ℝ} (hD : Coding.exponent S < D) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C :=
  entropy_bound_of_radial_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) hD (S.selfSimilar_radial μ hμ)

end EntropyRateDimension.System

end

end OAI
