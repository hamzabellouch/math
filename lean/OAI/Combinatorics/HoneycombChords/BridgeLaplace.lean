import OAI.Combinatorics.HoneycombChords.BridgeMass
import OAI.Combinatorics.HoneycombChords.LaplaceProfile

namespace OAI

/-!
# Height Laplace estimates for critical strict bridges

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb
open MeasureTheory Set Filter Topology StripExhaustion RenewalInput

/-- The height Laplace transform of the strict bridge mass. -/
noncomputable def bridgeLaplace (s : ℝ) : ℝ :=
  ∑' h : ℕ, Real.exp (-(s*h)) * (bridgeMass h).toReal

lemma bridgeMass_toReal_bounds : ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ h : ℕ,
    c*(1+(h:ℝ))^(-(1:ℝ)/4) ≤ (bridgeMass h).toReal ∧
    (bridgeMass h).toReal ≤ C*(1+(h:ℝ))^(-(1:ℝ)/4) := by
  obtain ⟨c,C,hc,hC,h⟩:=finiteBridgeMassEstimate
  refine ⟨c,C,hc,hC,fun n ↦ ?_⟩
  have hl:=ENNReal.toReal_mono (bridgeMass_finite n).ne (h n).1
  have hu:=ENNReal.toReal_mono ENNReal.ofReal_ne_top (h n).2
  rw [ENNReal.toReal_ofReal (by positivity : 0≤c*(1+(n:ℝ))^(-(1:ℝ)/4))] at hl
  rw [ENNReal.toReal_ofReal (by positivity : 0≤C*(1+(n:ℝ))^(-(1:ℝ)/4))] at hu
  exact ⟨hl,hu⟩

lemma bridgeLaplace_summable {s : ℝ} (hs : 0<s) :
    Summable (fun h : ℕ ↦ Real.exp (-(s*h)) * (bridgeMass h).toReal) := by
  obtain ⟨c,C,hc,hC,h⟩:=bridgeMass_toReal_bounds
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    ((laplaceProfile_summable hs).mul_left C)
  change Real.exp (-(s*n))*(bridgeMass n).toReal ≤ C*laplaceProfile s n
  unfold laplaceProfile
  nlinarith [mul_le_mul_of_nonneg_left (h n).2 (Real.exp_pos (-(s*n))).le]

/-- The height Laplace transform is comparable to `s^(-3/4)` for `0 < s ≤ 1`. -/
theorem bridgeLaplaceEstimate : ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ s : ℝ, 0<s → s≤1 →
    c*s^(-(3:ℝ)/4) ≤ bridgeLaplace s ∧ bridgeLaplace s ≤ C*s^(-(3:ℝ)/4) := by
  obtain ⟨c,C,hc,hC,h⟩:=bridgeMass_toReal_bounds
  refine ⟨c*(Real.exp (-1)*(2:ℝ)^(-(1:ℝ)/4)),
    C*(1+Real.Gamma (3/4)),by positivity,by positivity,?_⟩
  intro s hs hs1
  have hl : c*(∑' n : ℕ,laplaceProfile s n) ≤ bridgeLaplace s := by
    rw [←tsum_mul_left]
    apply Summable.tsum_le_tsum _ ((laplaceProfile_summable hs).mul_left c) (bridgeLaplace_summable hs)
    intro n
    change c*laplaceProfile s n ≤ Real.exp (-(s*n))*(bridgeMass n).toReal
    unfold laplaceProfile
    nlinarith [mul_le_mul_of_nonneg_left (h n).1 (Real.exp_pos (-(s*n))).le]
  have hu : bridgeLaplace s ≤ C*(∑' n : ℕ,laplaceProfile s n) := by
    rw [←tsum_mul_left]
    apply Summable.tsum_le_tsum _ (bridgeLaplace_summable hs) ((laplaceProfile_summable hs).mul_left C)
    intro n
    change Real.exp (-(s*n))*(bridgeMass n).toReal ≤ C*laplaceProfile s n
    unfold laplaceProfile
    nlinarith [mul_le_mul_of_nonneg_left (h n).2 (Real.exp_pos (-(s*n))).le]
  constructor
  · have hb:=mul_le_mul_of_nonneg_left (laplaceProfile_sum_lower hs hs1) hc.le
    nlinarith
  · have hb:=mul_le_mul_of_nonneg_left (laplaceProfile_sum_upper hs hs1) hC.le
    nlinarith

end CriticalHoneycomb

end

end OAI
