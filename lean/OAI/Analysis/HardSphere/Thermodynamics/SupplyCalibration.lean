import Mathlib
import OAI.Analysis.HardSphere.Bridges.NumericalSupply
import OAI.Analysis.HardSphere.Bridges.TrialScalarBound

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma supply_error_calibration {ell H D δ E : ℝ} {m j : ℕ}
    (hell : 0 < ell) (hH : 0 < H) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hm : ell*D/2 ≤ (m:ℝ)) (hj : (j:ℝ) ≤ H*D)
    (hδsmall : δ ≤ 1/140000) (hEsmall : (4*H*hitConstant/ell)*E ≤ 1/140000) :
    (m:ℝ≥0∞)*ENNReal.ofReal δ+(j:ℝ≥0∞)*(2*ENNReal.ofReal (hitConstant*E)) ≤
      ENNReal.ofReal ((m:ℝ)/70000) := by
  have hh : 0 ≤ hitConstant := hitConstant_pos.le
  have he : 2*(j:ℝ)*(hitConstant*E) ≤ (m:ℝ)/140000 := by
    have h₁ : 2*(j:ℝ)*(hitConstant*E) ≤ 2*(H*D)*(hitConstant*E) := by gcongr
    have h₂ : 2*(H*D)*(hitConstant*E) = (ell*D/2)*((4*H*hitConstant/ell)*E) := by field_simp; ring
    have h₃ := mul_le_mul_of_nonneg_left hEsmall (show 0 ≤ ell*D/2 by positivity)
    rw [←h₂] at h₃
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hδsmall (show 0 ≤ (m:ℝ) by positivity)
  have hfin : (m:ℝ)*δ+(j:ℝ)*(2*(hitConstant*E)) ≤ (m:ℝ)/70000 := by nlinarith
  have hx := ENNReal.ofReal_le_ofReal hfin
  simpa (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using hx

theorem source_supply_error_small {ell b A H C : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) (hC : 0 < C) :
    ∃ t₀ : ℝ,0<t₀ ∧ ∀ t : ℝ,0<t → t≤t₀ →
    ∀ Cn M c a : ℝ,0<c → 0<a → ∃D₀ : ℝ,1≤D₀ ∧
    ∀ D α : ℝ,∀m j : ℕ,D₀≤D → 0≤α → α≤A →
      ell*D/2≤(m:ℝ) → (m:ℝ)≤H*D → (j:ℝ)≤H*D →
      (m:ℝ≥0∞)*ENNReal.ofReal (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2))+
      (j:ℝ≥0∞)*(2*ENNReal.ofReal (hitConstant*(
        8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+(m:ℝ))+
        8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))))≤ENNReal.ofReal ((m:ℝ)/70000) := by
  have hhit : 0 < hitConstant := hitConstant_pos
  obtain ⟨t₁,ht₁,htail⟩ := trial_remainder_small (by norm_num : (0:ℝ)<1/140000)
  obtain ⟨t₂,ht₂,hcoll⟩ := collision_error_small hb hA hH hC
    (by positivity : 0 < 4*H*hitConstant/ell) (by norm_num : (0:ℝ)<1/140000)
  refine ⟨min t₁ t₂,lt_min ht₁ ht₂,?_⟩
  intro t ht htt Cn M c a hc ha
  obtain ⟨D₁,hD₁,hd₁⟩ := htail t ht (htt.trans (min_le_left _ _)) Cn M c a b hc ha
  obtain ⟨D₂,hD₂,hd₂⟩ := hcoll t ht (htt.trans (min_le_right _ _))
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D α m j hD hα hαA hm hmH hj
  have hDp : 1≤D := hD₁.trans ((le_max_left _ _).trans hD)
  have herr := hd₁ D ((le_max_left _ _).trans hD)
  have hcol := hd₂ D α (m:ℝ) ((le_max_right _ _).trans hD) hα hαA (by positivity) hmH
  have hEn : 0≤8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+(m:ℝ))+
      8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2) := by positivity

  have hδ : (0:ℝ) ≤ max 0 (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2)) := le_max_left _ _
  have hδs : max 0 (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2))≤1/140000 := max_le (by norm_num) herr
  have he := supply_error_calibration hell hH (zero_le_one.trans hDp) hδ hEn hm hj hδs hcol
  simpa only [ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (show (0:ℝ≥0∞)≤_ from zero_le)] using he

end HardSphere.Bridge

end
end

end

end OAI
