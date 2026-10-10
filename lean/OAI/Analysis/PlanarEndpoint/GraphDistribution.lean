import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.UnitReduction

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
namespace PlanarEndpoint

def SourceGraphDistribution (c₀ C₀ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
    ∀ v : Plane → ℂ, ∀ hv : MemLp v 2 volume,
    (∀ᵐ η : Plane ∂volume, η ∉ {η | c₀ ≤ ‖η‖ ∧ ‖η‖ ≤ C₀} → v η = 0) →
    ∀ (x₀ : Plane) (T : Plane → ℝ), Measurable T →
      (∀ X, T X ∈ Icc (0:ℝ) (L^2)) → ∀ lam : ℝ, 0 < lam →
      volume (Metric.ball x₀ (L^2) ∩ {X | lam < ‖frequencyExtension v X (T X)‖}) ≤
        ENNReal.ofReal (C * L^4 * (lam * L^(4/3:ℝ))^(-p) * ‖hv.toLp v‖^p)

lemma graphDistribution_scale_identity {L C lam : ℝ} (hL : 0 < L)
    (hC : 0 < C) (hlam : 0 < lam) {p : ℝ} (hp : p ≠ 0) {b : ℝ} (hb : 0 ≤ b) :
    C * L^4 * (lam * L^(4/3:ℝ))^(-p) * b^p =
      (L^2)^2 * (C^(p⁻¹) * (L^2)^(-2/3:ℝ) * b / lam)^p := by
  have hscale : (L^2)^(-2/3:ℝ) = (L^(4/3:ℝ))⁻¹ := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
    norm_num [Real.rpow_neg hL.le]
  rw [hscale, Real.div_rpow (by positivity) hlam.le,
    Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hC.le _) (by positivity)) hb,
    Real.mul_rpow (Real.rpow_nonneg hC.le _) (show 0 ≤ (L^(4/3:ℝ))⁻¹ by positivity),
    Real.rpow_inv_rpow hC.le hp, Real.inv_rpow (Real.rpow_nonneg hL.le _),
    Real.mul_rpow hlam.le (Real.rpow_nonneg hL.le _),
    Real.rpow_neg hlam.le, Real.rpow_neg (Real.rpow_nonneg hL.le _)]
  ring

lemma unitFrequencyGraphEstimate_of_source {c₀ C₀ p : ℝ} (hp : p ≠ 0)
    (hs : SourceGraphDistribution c₀ C₀ p) : UnitFrequencyGraphEstimate c₀ C₀ p := by
  obtain ⟨C,hC,hs⟩ := hs
  refine ⟨C^(p⁻¹),Real.rpow_pos_of_pos hC _,?_⟩
  intro R hR v hv hsup x₀ T hT hr lam hlam
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hL : 1 ≤ Real.sqrt R := by
    simpa using (Real.sqrt_le_sqrt hR)
  have hL0 : 0 < Real.sqrt R := lt_of_lt_of_le (by norm_num) hL
  have hsq : (Real.sqrt R)^2 = R := Real.sq_sqrt hR0
  have he := hs (Real.sqrt R) hL v hv hsup x₀ T hT (by simpa [hsq] using hr) lam hlam
  rw [graphDistribution_scale_identity hL0 hC hlam hp (norm_nonneg _),hsq] at he
  exact he

lemma sourceGraphDistribution_of_unitFrequency {c₀ C₀ p : ℝ} (hp : p ≠ 0)
    (hg : UnitFrequencyGraphEstimate c₀ C₀ p) : SourceGraphDistribution c₀ C₀ p := by
  obtain ⟨K,hK,hg⟩ := hg
  refine ⟨K^p,Real.rpow_pos_of_pos hK _,?_⟩
  intro L hL v hv hsup x₀ T hT hr lam hlam
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have he := hg (L^2) hL2 v hv hsup x₀ T hT hr lam hlam
  rw [graphDistribution_scale_identity hL0 (Real.rpow_pos_of_pos hK _) hlam hp
    (norm_nonneg _),Real.rpow_rpow_inv hK.le hp]
  exact he

lemma mainConclusion_of_sourceGraphDistribution {p : ℝ} (hp : 2 < p)
    (hs : SourceGraphDistribution (1/4) 4 p) {f : L2} (hf : InHThird f) :
    MainConclusion f :=
  mainConclusion_of_unitFrequencyGraph hp
    (unitFrequencyGraphEstimate_of_source (by linarith) hs) hf

end PlanarEndpoint
end

end OAI
