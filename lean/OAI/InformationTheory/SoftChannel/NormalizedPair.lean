import OAI.InformationTheory.BooleanNoise.NormalizedPair
import OAI.InformationTheory.SoftChannel.LRegularity

namespace OAI

section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem NormalizedPair_normalized_pair_bound_of_antitone
    (hanti : AntitoneOn L (Set.Ioi 0)) {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b := by
  have hA := normalized_pair_scale_pos hab
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hlow : 0 < ell - pairEntropyGap a b / (1 - a ^ 2) := sub_pos.mpr hs1
  have ha : |a| ≤ 1 :=
    (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) hab).le
  have hH := ell_mul_one_sub_sq_le_entropy ha
  have hratio : ell - pairEntropyGap a b / (1 - a ^ 2) ≤
      ((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2) := by
    apply (le_div_iff₀ hA).mpr
    calc
      (ell - pairEntropyGap a b / (1 - a ^ 2)) * (1 - a ^ 2) =
          ell * (1 - a ^ 2) - pairEntropyGap a b := by
        field_simp
      _ ≤ entropy a - pairEntropyGap a b := sub_le_sub_right hH _
      _ = (entropy (a + b) + entropy (a - b)) / 2 := by
        unfold pairEntropyGap
        ring
  have hL := hanti hlow (hlow.trans_le hratio) hratio
  rw [L_ell_sub hs0 hs1] at hL
  have hr := normalized_pair_dissipation_ge_r hab
  have hbound :
      L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        (pairDissipation a b - 2 * pairEntropyGap a b) / (1 - a ^ 2) := by
    calc
      _ ≤ r (pairEntropyGap a b / (1 - a ^ 2)) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := hL
      _ ≤ pairDissipation a b / (1 - a ^ 2) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := sub_le_sub_right hr _
      _ = _ := by ring
  simpa only [mul_comm] using (le_div_iff₀ hA).mp hbound

end LeanBlast.CourtadeKumar
end

end OAI
