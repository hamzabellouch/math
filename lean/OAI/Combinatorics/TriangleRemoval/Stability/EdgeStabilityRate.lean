import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeRadius
import OAI.Combinatorics.TriangleRemoval.Process.TriangleIndex

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def edgeStabilityRate (s t Q : ℝ) : ℝ := s^2/(Q*t)
noncomputable def edgeStabilityScalar (s t Q κ : ℝ) : ℝ := s/t-1-2*edgeStabilityRate s t Q+κ*s/(Q*t)

lemma triangle_relative_inverse_bound {Q S r : ℝ} (hS : 0 < S) (hr : r ≤ 1/2)
    (h : |Q/S-1| ≤ r) : 0 < Q ∧ |1-S/Q| ≤ 2*r ∧ S/Q ≤ 2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have hlow : S/2 ≤ Q := by
    have hh : 1/2 ≤ Q/S := by linarith
    have hh' := (le_div_iff₀ hS).mp hh
    linarith only [hh']
  have hQ : 0 < Q := lt_of_lt_of_le (by positivity) hlow
  have hab : |Q-S| ≤ r*S := by
    have he : Q/S-1 = (Q-S)/S := by field_simp
    rw [he,abs_div,abs_of_pos hS] at h
    exact (div_le_iff₀ hS).mp h
  have hratio : S/Q ≤ 2 := (div_le_iff₀ hQ).mpr (by linarith)
  have hr0 : 0 ≤ r := (abs_nonneg _).trans h
  refine ⟨hQ,?_,hratio⟩
  have he : 1-S/Q = (Q-S)/Q := by field_simp
  rw [he,abs_div,abs_of_pos hQ]
  calc
    _ ≤ r*S/Q := div_le_div_of_nonneg_right hab hQ.le
    _ = r*(S/Q) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hratio hr0]

lemma edge_stability_coefficients {s t Q S lam r κ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hS : 0 < S) (hl : 0 ≤ lam)
    (hscale : t = s*(1-lam)^2) (hratio : s ≤ 2*t)
    (hident : s = lam*S) (hr : r ≤ 1/2) (hQerr : |Q/S-1| ≤ r)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (0 ≤ edgeStabilityRate s t Q ∧ edgeStabilityRate s t Q ≤ 4*lam) ∧
      |edgeStabilityScalar s t Q κ| ≤ 8*r*lam+2*lam^2+4*lam/s := by
  obtain ⟨hQ,habs,hSQ⟩ := triangle_relative_inverse_bound hS hr hQerr
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hQerr
  have hsQ : s/Q ≤ 2*lam := by
    rw [hident,mul_div_assoc]
    simpa only [mul_comm lam 2] using mul_le_mul_of_nonneg_left hSQ hl
  have hsQdiff : |lam-s/Q| ≤ 2*r*lam := by
    have he : lam-s/Q = lam*(1-S/Q) := by rw [hident]; ring
    rw [he,abs_mul,abs_of_nonneg hl]
    nlinarith only [mul_le_mul_of_nonneg_left habs hl]
  have hsT : s/t ≤ 2 := (div_le_iff₀ ht).mpr hratio
  have haeq : edgeStabilityRate s t Q = (s/t)*(s/Q) := by unfold edgeStabilityRate; ring
  have hbeq : edgeStabilityScalar s t Q κ =
      (s/t)*(2*(lam-s/Q)-lam^2+κ/Q) := by
    unfold edgeStabilityScalar edgeStabilityRate
    apply (mul_right_cancel₀ ht.ne')
    field_simp [hs.ne',ht.ne',hQ.ne']
    rw [hscale]
    ring
  constructor
  · rw [haeq]
    exact ⟨by positivity,(mul_le_mul hsT hsQ (by positivity) (by norm_num)).trans_eq (by ring)⟩
  · have hκQ : |κ/Q| ≤ 2*lam/s := by
      rw [abs_of_nonneg (div_nonneg hκ hQ.le)]
      apply (le_div_iff₀ hs).mpr
      have hh := div_le_div_of_nonneg_right hκ1 hQ.le
      have hm := mul_le_mul_of_nonneg_right hh hs.le
      calc
        _ ≤ (1/Q)*s := hm
        _ = s/Q := by ring
        _ ≤ _ := hsQ
    have hb : |2*(lam-s/Q)-lam^2+κ/Q| ≤ 4*r*lam+lam^2+2*lam/s := by
      calc
        _ ≤ |2*(lam-s/Q)-lam^2|+|κ/Q| := abs_add_le _ _
        _ ≤ |2*(lam-s/Q)|+|lam^2|+|κ/Q| := by linarith only [abs_sub (2*(lam-s/Q)) (lam^2)]
        _ ≤ 4*r*lam+lam^2+2*lam/s := by
          rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg (sq_nonneg lam)]
          linarith only [hsQdiff,hκQ]
    rw [hbeq,abs_mul,abs_of_pos (div_pos hs ht)]
    calc
      _ ≤ 2*(4*r*lam+lam^2+2*lam/s) := mul_le_mul hsT hb (abs_nonneg _) (by norm_num)
      _ = _ := by ring

lemma early_codegree_grid {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n) :
    earlyTemplateScale 1 2 n (i+1) = earlyTemplateScale 1 2 n i*
      (1-6/(n : ℝ)^2/earlyDensity n i)^2 ∧
    earlyTemplateScale 1 2 n i = (6/(n : ℝ)^2/earlyDensity n i)*earlyTriangleScale n i ∧
    0 ≤ 6/(n : ℝ)^2/earlyDensity n i ∧
    6/(n : ℝ)^2/earlyDensity n i ≤ 6/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := early_density_positive hn hp hi.le
  have hs := earlyDensity_succ n i
  have he : earlyDensity n (i+1) = earlyDensity n i*(1-6/(n : ℝ)^2/earlyDensity n i) := by
    have he : earlyDensity n (i+1) = earlyDensity n i-6/(n : ℝ)^2 := by linarith only [hs]
    rw [he]
    field_simp
  refine ⟨?_,?_,by positivity,?_⟩
  · simp only [earlyTemplateScale,pow_one,he,mul_pow]; ring
  · unfold earlyTriangleScale
    simp only [earlyTemplateScale,pow_one]
    field_simp
  · have hp' := hp.trans (earlyDensity_antitone n hi.le)
    apply (div_le_iff₀ hpi).mpr
    have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
    convert hm using 1
    field_simp

end SharpTerminalLeave
end
end

end OAI
