import OAI.MeasureTheory.Falconer.Geometry.PointBallCounts
import OAI.MeasureTheory.Falconer.Estimates.RescaledConditional

namespace OAI

/-! Every closed-ball test follows from the finite dyadic prefix tests.
This applies directly to original finite points, with no center replacement. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem finite_prefix_ball_bound_at {N M : ℕ} (hMN : M ≤ N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n ≤ M, ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^n)^s*(P.card:ℝ)) :
    NormalizedFiniteBallBound (1/(2:ℝ)^M) s (49*K*4^s) P := by
  intro z r hr _
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^M).trans_le hr
  by_cases hsmall : 2*r ≤ 1
  · have hmin : 1/(2:ℝ)^M ≤ 2*r := hr.trans (by linarith only [hr0])
    obtain ⟨n,hn,hlo,hup⟩ := dyadic_radius_bracket hmin hsmall
    have hbound := finite_point_ball_count Q (by rw [hQ]; norm_num) hleaf (hn.trans hMN) hr0
      (by positivity : 0 ≤ K*(1/(2:ℝ)^n)^s*(P.card:ℝ))
      (by simpa only [hQ] using hlo) (hprefix n hn) z
    have hpow : (1/(2:ℝ)^n)^s ≤ (4*r)^s := Real.rpow_le_rpow (by positivity)
      (by linarith only [hup]) hs
    calc
      _ ≤ (49:ℝ)*(K*(1/(2:ℝ)^n)^s*(P.card:ℝ)) := by
        simpa only [Nat.reducePow,Nat.cast_ofNat] using hbound
      _ ≤ (49:ℝ)*(K*(4*r)^s*(P.card:ℝ)) := by gcongr
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring
  · have hpow : 1 ≤ (4*r)^s := Real.one_le_rpow (by linarith only [hsmall]) hs
    have hlarge : 1 ≤ 49*K*(4*r)^s := by nlinarith only [mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)]
    calc
      _ ≤ (P.card:ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ (49*K*(4*r)^s)*(P.card:ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hlarge
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem finite_prefix_ball_bound {N : ℕ} {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n ≤ N, ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^n)^s*(P.card:ℝ)) :
    NormalizedFiniteBallBound (1/(2:ℝ)^N) s (49*K*4^s) P :=
  finite_prefix_ball_bound_at le_rfl hs hK Q hQ P l hleaf hprefix

end Falconer

end OAI
