import OAI.MeasureTheory.Falconer.Estimates.DyadicCenters

namespace OAI

/-! # Separation of distinct actual dyadic centers in any dimension -/

namespace Falconer

theorem DyadicCube.centers_separated {d n : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {p q : List (Fin d → Bool)} (hp : p.length = n) (hq : q.length = n) (hpq : p ≠ q) :
    Q.side/(2:ℝ)^n ≤ dist (Q.descendant p).center (Q.descendant q).center := by
  classical
  have hcode : dyadicCode p ≠ dyadicCode q := fun h => hpq (dyadicCode_injective_at_depth hp hq h)
  have hex : ∃ i, dyadicCode p i ≠ dyadicCode q i := by
    by_contra h
    push Not at h
    exact hcode (funext h)
  obtain ⟨i,hi⟩ := hex
  have hz : (1:ℤ) ≤ |dyadicCode p i-dyadicCode q i| := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi) with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hr : (1:ℝ) ≤ |(dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)| := by exact_mod_cast hz
  have hs : 0 < Q.side/(2:ℝ)^n := by positivity
  have hcoord : (Q.descendant p).center i-(Q.descendant q).center i =
      (Q.side/(2:ℝ)^n)*((dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)) := by
    rw [Q.descendant_center,Q.descendant_center,hp,hq]
    ring
  have hb := PiLp.norm_apply_le ((Q.descendant p).center-(Q.descendant q).center) i
  change |(Q.descendant p).center i-(Q.descendant q).center i| ≤
    ‖(Q.descendant p).center-(Q.descendant q).center‖ at hb
  rw [hcoord,abs_mul,abs_of_pos hs] at hb
  rw [dist_eq_norm]
  nlinarith

end Falconer

end OAI
