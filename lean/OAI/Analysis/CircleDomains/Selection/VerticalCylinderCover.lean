import OAI.Analysis.CircleDomains.Modulus.LengthContent
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! A narrow vertical cylinder has a finite small-diameter cover whose
quadratic cost is controlled by its height times its base radius. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma vertical_cylinder_cover (c : ℝ × ℝ) (t : ℝ) {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hdR : d ≤ 4*R) :
    ∃ (N : ℕ) (T : Fin N → Set ((ℝ × ℝ) × ℝ)),
      closedBall c d ×ˢ Icc (t-R) (t+R) ⊆ ⋃ i, T i ∧
      (∀ i, ediam (T i) ≤ ENNReal.ofReal (2*d)) ∧
      (N : ℝ)*(2*d)^2 ≤ 32*R*d := by
  let N := Nat.floor (2*R/d)+1
  let T : Fin N → Set ((ℝ × ℝ) × ℝ) := fun i =>
    closedBall c d ×ˢ closedBall (t-R+(i:ℕ)*d) d
  refine ⟨N,T,?_,?_,?_⟩
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    let w := (y-(t-R))/d
    have hw0 : 0 ≤ w := div_nonneg (by linarith [hy.1]) hd.le
    have hwR : w ≤ 2*R/d := (div_le_div_iff_of_pos_right hd).mpr (by linarith [hy.2])
    let k := Nat.floor w
    have hk : k < N := Nat.lt_succ_of_le (Nat.floor_mono hwR)
    apply mem_iUnion.mpr
    refine ⟨⟨k,hk⟩,hx,?_⟩
    change dist y (t-R+(k:ℝ)*d) ≤ d
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hlo := (le_div_iff₀ hd).mp (Nat.floor_le hw0)
    have hhi := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one w)
    dsimp only [w, k] at hlo hhi ⊢
    constructor <;> nlinarith
  · intro i
    change ediam (closedBall c d ×ˢ closedBall (t-R+(i:ℕ)*d) d) ≤ _
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    rw [Prod.dist_eq]
    apply max_le
    · have htri := dist_triangle x.1 c y.1
      rw [dist_comm c y.1] at htri
      linarith [mem_closedBall.mp hx.1, mem_closedBall.mp hy.1]
    · have htri := dist_triangle x.2 (t-R+(i:ℕ)*d) y.2
      rw [dist_comm (t-R+(i:ℕ)*d) y.2] at htri
      linarith [mem_closedBall.mp hx.2, mem_closedBall.mp hy.2]
  · have hN : (N : ℝ) ≤ 2*R/d+1 := by
      dsimp only [N]
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.floor_le (div_nonneg (show 0 ≤ 2*R by positivity) hd.le)) le_rfl
    have hNd : (N : ℝ)*d ≤ 2*R+d := by
      have h := mul_le_mul_of_nonneg_right hN hd.le
      field_simp [hd.ne'] at h
      nlinarith
    nlinarith

end CircleDomainRigidity

end

end OAI
