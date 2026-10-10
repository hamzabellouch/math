import OAI.Analysis.HenonEmden.RelativePressure

namespace OAI

section RelativeLocalization

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden
open Cutoff

def localQ {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  ∫ z : Space n × Space n, fluxFactor n z-eta n z.1+w n z.1*radialFactor z ∂interaction f g

lemma IsSolution.localQ_identity {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    localQ (source u q B) (source v p A) =
      (∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A))-weightedEnergy (eta n) u q B+
        (∫ z : Space n × Space n, w n z.1*radialFactor z ∂interaction (source u q B) (source v p A)) := by
  have hη := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hi : Integrable (fun z : Space n × Space n => fluxFactor n z-eta n z.1) _ :=
    (h.integrable_fluxFactor hn hp hq).sub hη.1
  rw [localQ,integral_add hi (h.integrable_radialWeight hn hq),
    integral_sub (h.integrable_fluxFactor hn hp hq) hη.1,hη.2]

lemma IsSolution.local_errors_le {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    |localQ (source u q B) (source v p A)|+|weightedEnergy (eta n) u q B-weightedEnergy (eta n) v p A| ≤
      ∫ z, localError z ∂interaction (source u q B) (source v p A) := by
  have hηf := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hηg := h.weight_right hn hp (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hi : Integrable (fun z : Space n × Space n => fluxFactor n z-eta n z.1+w n z.1*radialFactor z) _ :=
    ((h.integrable_fluxFactor hn hp hq).sub hηf.1).add (h.integrable_radialWeight hn hq)
  have hj : Integrable (fun z : Space n × Space n => eta n z.1-eta n z.2) _ := hηf.1.sub hηg.1
  unfold localQ localError
  rw [integral_add hi.abs hj.abs,← hηf.2,← hηg.2,← integral_sub hηf.1 hηg.1]
  exact add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs

lemma localization_relative {n : ℕ} (hn : 2 ≤ n) {p q A B ε : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
      |localQ (source u q B) (source v p A)|+|weightedEnergy (eta n) u q B-weightedEnergy (eta n) v p A| ≤
        ε*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+C := by
  let δ := min (1/4) (ε/(closeConstant n+1))
  have hC := closeConstant_nonneg n
  have hden : 0 < closeConstant n+1 := by linarith
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδε : closeConstant n*δ ≤ ε := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (1/4) (ε/(closeConstant n+1)))
    change δ*(closeConstant n+1) ≤ ε at hh
    nlinarith
  refine ⟨localizationConstant n p q A B δ,localizationConstant_nonneg p q A B hδ.le,?_⟩
  intro u v h
  have he := (h.local_errors_le hn hp hq).trans (h.localError_bound hn hp hq hδ hδ1).2
  have hE : 0 ≤ weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A :=
    add_nonneg (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_u x).le))
      (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le))
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hδε hE) le_rfl)

lemma IsSolution.closing_identity {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (((n:ℝ)+B)/(q+1)-((n:ℝ)-2))*weightedEnergy (eta n) u q B+
      (((n:ℝ)+A)/(p+1))*weightedEnergy (eta n) v p A =
        (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
        radialPressure (source u q B) (source v p A)+((n:ℝ)-2)*localQ (source u q B) (source v p A) := by
  have hh := h.symmetric_virial hn hp hq
  rw [h.localQ_identity hn hp hq,radialPressure]
  nlinarith [hh]

end HenonLaneEmden
end
end RelativeLocalization

end OAI
