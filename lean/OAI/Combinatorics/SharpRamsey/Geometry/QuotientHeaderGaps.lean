import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationGapCosts
import OAI.Combinatorics.SharpRamsey.Parameters.ProjectionScales

namespace OAI

section
namespace SharpLogRamsey.Projection
open Real

lemma quotient_gap_bounds {q U UT Z W N A T B : ℝ}
    (hq : 0<q) (hN : 0<N) (hT : 0<T) (hA : 0<A) (hB : 0<B)
    (hNA : (9/10:ℝ)*N≤A) (hTB : T/(3*q)≤B)
    (hAU : A≤Z) (hBW : B≤W) (hZU : Z≤U) (hW : W≤100*UT/q) :
    log (Z/A) ≤ log (U/N)+1 ∧ log (W/B) ≤ log (UT/T)+299 := by
  have hU : 0<U := lt_of_lt_of_le hA (hAU.trans hZU)
  have hUT : 0<UT := by
    have hh : 0<100*UT/q := lt_of_lt_of_le hB (hBW.trans hW)
    have hh' := (div_pos_iff.mp hh)
    rcases hh' with hh'|hh'
    · linarith [hh'.1]
    · linarith [hh'.2]
  have hZU' : 0<Z := lt_of_lt_of_le hA hAU
  have hW' : 0<W := lt_of_lt_of_le hB hBW
  have h1 : Z/A≤2*(U/N) := by
    apply (div_le_iff₀ hA).mpr
    have ha : N≤2*A := by linarith
    have hh := mul_le_mul_of_nonneg_left ha (le_of_lt (div_pos hU hN))
    rw [div_mul_cancel₀ _ (ne_of_gt hN)] at hh
    nlinarith only [hh,hZU]
  have h2 : W/B≤300*(UT/T) := by
    apply (div_le_iff₀ hB).mpr
    have hb := (div_le_iff₀ (by positivity : 0<3*q)).mp hTB
    have hh := mul_le_mul_of_nonneg_left hb (show 0≤100*UT/(q*T) by positivity)
    have he1 : 100*UT/(q*T)*T=100*UT/q := by field_simp
    have he2 : 100*UT/(q*T)*(B*(3*q))=300*(UT/T)*B := by field_simp; ring
    rw [he1,he2] at hh
    exact hW.trans hh
  constructor
  · have hh := log_le_log (div_pos hZU' hA) h1
    rw [log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt (div_pos hU hN))] at hh
    have hc := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  · have hh := log_le_log (div_pos hW' hB) h2
    rw [log_mul (by norm_num : (300:ℝ)≠0) (ne_of_gt (div_pos hUT hT))] at hh
    have hc := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<300)
    linarith

end SharpLogRamsey.Projection

end

end OAI
