import Mathlib

namespace OAI

open Set Filter
open scoped Topology

namespace Percolation.BenjaminiSchramm

theorem magnetization_ratio_bound_of_quartic_moment
    (M d : ℝ → ℝ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hd : ∀ h, 0 < h → HasDerivAt M (d h) h)
    (hM : ∀ h, 0 < h → 0 ≤ M h)
    (hmoment : ∀ t, 0 < t → t ≤ 1 → M (t ^ 4) ≤ K * t ^ 3)
    (hconcave : ∀ h, 0 < h → h * d h ≤ M h)
    (hdiff : ∀ t, 0 < t → t ≤ 1 →
      M (t ^ 4) ≤ C * M (t ^ 4) ^ 2 + t ^ 4 * d (t ^ 4) + C * t ^ 6 * d (t ^ 4))
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    M (t ^ 4) / t ^ 4 ≤ M 1 + 2 * C * K ^ 2 + 4 * C * K := by
  let F (s : ℝ) := M (s ^ 4) / s ^ 4 + 2 * C * K ^ 2 * s ^ 2 + 4 * C * K * s
  let D (s : ℝ) :=
    ((d (s ^ 4) * (4 * s ^ 3)) * s ^ 4 - M (s ^ 4) * (4 * s ^ 3)) / (s ^ 4) ^ 2 +
      4 * C * K ^ 2 * s + 4 * C * K
  have hF (s : ℝ) (hs : 0 < s) : HasDerivAt F (D s) s := by
    have hp4 : HasDerivAt (fun r : ℝ => r ^ 4) (4 * s ^ 3) s := by
      convert (hasDerivAt_id s).pow 4 using 1
      · funext r
        rfl
      · norm_num
    have hp2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
      convert (hasDerivAt_id s).pow 2 using 1
      · funext r
        rfl
      · norm_num
    have hm : HasDerivAt (fun r : ℝ => M (r ^ 4))
        (d (s ^ 4) * (4 * s ^ 3)) s :=
      (hd (s ^ 4) (pow_pos hs 4)).comp (h := fun r : ℝ => r ^ 4) s hp4
    convert ((hm.div hp4 (pow_ne_zero 4 hs.ne')).add
      (hp2.const_mul (2 * C * K ^ 2))).add ((hasDerivAt_id s).const_mul (4 * C * K)) using 1
    · funext r
      rfl
    · dsimp [D]
      ring
  have hD (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : 0 ≤ D s := by
    have hmom := hmoment s hs hs1
    have hsq : M (s ^ 4) ^ 2 ≤ K ^ 2 * s ^ 6 := by
      calc
        _ ≤ (K * s ^ 3) ^ 2 :=
          (sq_le_sq₀ (hM _ (pow_pos hs 4)) (mul_nonneg hK (pow_nonneg hs.le 3))).mpr hmom
        _ = _ := by ring
    have hterm : s ^ 6 * d (s ^ 4) ≤ K * s ^ 5 := by
      calc
        _ = s ^ 2 * (s ^ 4 * d (s ^ 4)) := by ring
        _ ≤ s ^ 2 * M (s ^ 4) :=
          mul_le_mul_of_nonneg_left (hconcave _ (pow_pos hs 4)) (sq_nonneg s)
        _ ≤ s ^ 2 * (K * s ^ 3) := mul_le_mul_of_nonneg_left hmom (sq_nonneg s)
        _ = _ := by ring
    have herror : 0 ≤ s ^ 4 * d (s ^ 4) - M (s ^ 4) + C * K ^ 2 * s ^ 6 + C * K * s ^ 5 := by
      have hsqC := mul_le_mul_of_nonneg_left hsq hC
      have htermC := mul_le_mul_of_nonneg_left hterm hC
      nlinarith [hdiff s hs hs1]
    have hn : 0 ≤ ((d (s ^ 4) * (4 * s ^ 3)) * s ^ 4 - M (s ^ 4) * (4 * s ^ 3)) +
        (s ^ 4) ^ 2 * (4 * C * K ^ 2 * s + 4 * C * K) := by
      convert mul_nonneg (by positivity : 0 ≤ 4 * s ^ 3) herror using 1
      ring
    have hden : 0 < (s ^ 4) ^ 2 := pow_pos (pow_pos hs 4) 2
    dsimp [D]
    rw [add_assoc, div_add' _ _ _ hden.ne']
    exact div_nonneg (by nlinarith [hn]) hden.le
  have hmono : MonotoneOn F (Icc t 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t 1)
      (fun s hs => (hF s (ht.trans_le hs.1)).continuousAt.continuousWithinAt)
      (fun s hs => (hF s (ht.trans_le (interior_subset hs).1)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hmem := interior_subset hs
    rw [(hF s (ht.trans_le hmem.1)).deriv]
    exact hD s (ht.trans_le hmem.1) hmem.2
  have hb := hmono ⟨le_rfl,ht1⟩ ⟨ht1,le_rfl⟩ ht1
  dsimp [F] at hb
  norm_num only [one_pow, div_one, mul_one] at hb
  have hnonneg1 : 0 ≤ 2 * C * K ^ 2 * t ^ 2 := by positivity
  have hnonneg2 : 0 ≤ 4 * C * K * t := by positivity
  linarith

end Percolation.BenjaminiSchramm

end OAI
