import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma integral_squared_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → ℝ) (hM : Measurable M)
    (C : ℝ) (hbound : ∀ ω, ‖M ω‖ ≤ C) (b : ℝ) :
    (∫ ω, (M ω-b)^2 ∂μ) = (∫ ω, (M ω)^2 ∂μ)-2*b*(∫ ω, M ω ∂μ)+b^2 := by
  have hi : Integrable M μ := Integrable.of_bound hM.aestronglyMeasurable C (ae_of_all _ hbound)
  have his : Integrable (fun ω => (M ω)^2) μ :=
    Integrable.of_bound (hM.pow_const 2).aestronglyMeasurable (C^2) (ae_of_all _ (fun ω => by
      simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2))
  have hh : (fun ω => (M ω-b)^2) = (fun ω => (M ω)^2-2*b*M ω+b^2) := by funext ω; ring
  have hid : Integrable (fun ω => (M ω)^2-2*b*M ω) μ := his.sub (hi.const_mul (2*b))
  rw [hh,integral_add hid (integrable_const (b^2)),
    integral_sub his (hi.const_mul (2*b)),integral_const_mul]
  simp

lemma squared_error_tendsto_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hM : ∀ i, Measurable (M i)) (C : ℝ) (hbound : ∀ i ω, ‖M i ω‖ ≤ C)
    (b : ℝ) (hfirst : Tendsto (fun i => ∫ ω, M i ω ∂μ) atTop (𝓝 b))
    (hsecond : Tendsto (fun i => ∫ ω, (M i ω)^2 ∂μ) atTop (𝓝 (b^2))) :
    Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂μ) atTop (𝓝 0) := by
  have hh := (hsecond.sub (hfirst.const_mul (2*b))).add_const (b^2)
  have hb : b^2-2*b*b+b^2 = 0 := by ring
  simpa only [integral_squared_error μ _ (hM _) C (hbound _) b,hb] using hh

lemma tendstoInMeasure_of_squared_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℕ → Ω → ℝ) (b : ℝ)
    (hi : ∀ i, Integrable (fun ω => (M i ω-b)^2) μ)
    (hl : Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ M atTop (fun _ => b) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hb (i : ℕ) : μ.real {ω | ε ≤ ‖M i ω-b‖} ≤ (∫ ω, (M i ω-b)^2 ∂μ)/(ε^2) := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun ω => sq_nonneg (M i ω-b))) (hi i) (ε^2)
    have hs : {ω | ε ≤ ‖M i ω-b‖} = {ω | ε^2 ≤ (M i ω-b)^2} := by
      ext ω
      change ε ≤ ‖M i ω-b‖ ↔ ε^2 ≤ (M i ω-b)^2
      simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg (M i ω-b))).symm
    rw [hs,mul_comm]
    exact hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun i => (∫ ω, (M i ω-b)^2 ∂μ)/(ε^2)) atTop (𝓝 0) from by simpa using hl.div_const (ε^2))
    (fun _ => measureReal_nonneg) hb

lemma tendstoInMeasure_of_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] (hac : μ ≪ ν)
    (M : ℕ → Ω → ℝ) (hM : ∀ i, Measurable (M i)) (b : ℝ)
    (hl : TendstoInMeasure ν M atTop (fun _ => b)) :
    TendstoInMeasure μ M atTop (fun _ => b) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun i => (hM i).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ns',hns',hh⟩ := (hl.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ns',hns',hac.ae_le hh⟩

end DirectionalTransience

end

end

end OAI
