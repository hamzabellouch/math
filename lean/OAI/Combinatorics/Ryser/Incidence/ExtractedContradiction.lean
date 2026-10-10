import OAI.Combinatorics.Ryser.Incidence.NoApproximateSubfield
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem extracted_card_constraints
    (q r V K s : ℝ) (hq : 0 < q) (hr : 0 < r) (hrq : r ^ 2 = q)
    (hV : 0 < V) (hK : 0 ≤ K)
    (hlo : 3 * r / (8 * V ^ 2) ≤ s) (hhi : s ≤ V * r)
    (hfirst : 32 * V ^ 2 * K ^ 127942 < 3 * r)
    (hsecond : 4096 * V ^ 6 * K ^ 3 < 27 * r)
    (hthird : 2 * K ^ 527 * V ≤ r) :
    4 * K ^ 127942 < s ∧ 8 * K ^ 3 * q < s ^ 3 ∧
      2 * K ^ 527 * s ≤ q := by
  let _ := hq
  have hden : 0 < 8 * V ^ 2 := by positivity
  have hlo' : 3 * r ≤ s * (8 * V ^ 2) := (div_le_iff₀ hden).mp hlo
  have hlarge : 4 * K ^ 127942 < s := by
    apply lt_of_lt_of_le _ hlo
    apply (lt_div_iff₀ hden).mpr
    have heq : 4 * K ^ 127942 * (8 * V ^ 2) = 32 * V ^ 2 * K ^ 127942 := by ring
    rw [heq]
    exact hfirst
  have hfactor : 0 < 512 * V ^ 6 := by positivity
  have hcubic : 8 * K ^ 3 * q < s ^ 3 := by
    apply (mul_lt_mul_iff_left₀ hfactor).mp
    calc
      (8 * K ^ 3 * q) * (512 * V ^ 6) < 27 * r ^ 3 := by
        rw [← hrq]
        calc
          (8 * K ^ 3 * r ^ 2) * (512 * V ^ 6) =
              (4096 * V ^ 6 * K ^ 3) * r ^ 2 := by ring
          _ < (27 * r) * r ^ 2 := mul_lt_mul_of_pos_right hsecond (pow_pos hr 2)
          _ = 27 * r ^ 3 := by ring
      _ = (3 * r) ^ 3 := by ring
      _ ≤ (s * (8 * V ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * r) hlo' 3
      _ = s ^ 3 * (512 * V ^ 6) := by ring
  refine ⟨hlarge, hcubic, ?_⟩
  calc
    2 * K ^ 527 * s ≤ 2 * K ^ 527 * (V * r) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = (2 * K ^ 527 * V) * r := by ring
    _ ≤ r * r := mul_le_mul_of_nonneg_right hthird hr.le
    _ = q := by rw [← pow_two, hrq]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
open scoped Pointwise

theorem extracted_set_contradiction
    (S : Finset F) (r V K : ℝ) (hzero : (0 : F) ∉ S)
    (hK : 2 ≤ K) (hV : 0 < V) (hr : 0 < r)
    (hrq : r ^ 2 = (Fintype.card F : ℝ))
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hdiv : ((S / S).card : ℝ) ≤ K * S.card)
    (hproper : ∀ L : Subfield F, L ≠ ⊤ →
      (Nat.card L : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hlo : 3 * r / (8 * V ^ 2) ≤ (S.card : ℝ))
    (hhi : (S.card : ℝ) ≤ V * r)
    (hfirst : 32 * V ^ 2 * K ^ 127942 < 3 * r)
    (hsecond : 4096 * V ^ 6 * K ^ 3 < 27 * r)
    (hthird : 2 * K ^ 527 * V ≤ r) : False := by
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  obtain ⟨hlarge, hcubic, hupper⟩ := extracted_card_constraints
    (Fintype.card F) r V K S.card hq hr hrq hV hK0 hlo hhi hfirst hsecond hthird
  rcases no_approximate_subfield_finite S K hzero hK hsub hdiv hproper hlarge with h | h
  · exact (not_le_of_gt hcubic) h
  · exact (not_lt_of_ge hupper) h

end RyserCoveringCounterexample.Incidence

end OAI
