import OAI.Probability.ContinuumTransition.QuadraticTransform

namespace OAI

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

lemma quadratic_bound_attains {f : ℝ → ℝ} (hf : Continuous f) {A B c : ℝ} (hc : 0 < c)
    (hb : ∀ d, f d ≤ A+B*|d|-c*d^2) : ∃ d, ∀ r, f r ≤ f d := by
  let D : ℝ := max 1 (max (2*|B|/c) (2*|A-f 0|/c))
  have hD : 1 ≤ D := le_max_left _ _
  have hDB : 2*|B|/c ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 2*|A-f 0|/c ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hB : 2*|B| ≤ c*D := by have := (div_le_iff₀ hc).mp hDB; linarith
  have hA : 2*|A-f 0| ≤ c*D := by have := (div_le_iff₀ hc).mp hDA; linarith
  have hout (r : ℝ) (hr : D < |r|) : f r ≤ f 0 := by
    have hr1 : 1 ≤ |r| := hD.trans hr.le
    have hb' := hb r
    have hs : |r|^2 = r^2 := sq_abs r
    have hbmul := mul_le_mul_of_nonneg_right hB (abs_nonneg r)
    have hDmul := mul_le_mul_of_nonneg_left hr.le (show 0 ≤ c*|r| by positivity)
    have hDmul' := mul_le_mul_of_nonneg_left hr.le hc.le
    have hrmul := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ c*|r| by positivity)
    have hbm := mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg r)
    have ha := le_abs_self (A-f 0)
    nlinarith
  obtain ⟨d,hd,hmax⟩ := (isCompact_Icc : IsCompact (Icc (-D) D)).exists_isMaxOn
    (show (Icc (-D) D).Nonempty from ⟨0,by constructor <;> linarith⟩) hf.continuousOn
  refine ⟨d,fun r => ?_⟩
  by_cases hr : |r| ≤ D
  · exact hmax (abs_le.mp hr)
  · exact (hout r (lt_of_not_ge hr)).trans (hmax (show (0 : ℝ) ∈ Icc (-D) D by constructor <;> linarith))

lemma quadratic_upper_bound {Q H : ℝ → ℝ} {c b k : ℝ} (hc : 0 < c)
    (hQ : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q h))
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) (h : ℝ) :
    Q h ≤ (h+b)^2/(4*c)+k := by
  apply (hQ h).2
  rintro _ ⟨d,hd,rfl⟩
  have hh := hH d hd
  have hs := sq_nonneg (2*c*d-(h+b))
  have he : ((h+b)^2/(4*c))*(4*c) = (h+b)^2 := by field_simp
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 4*c by positivity)
  nlinarith

end ContinuumTemperature
end

end OAI
