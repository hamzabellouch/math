import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateProfile
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGeometricAfter

namespace OAI

/-! Summable quantitative tails outside the two finite coordinate boxes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimary_box_geometric (k : ℕ) :
    ((cubicThetaIntegerBox k).card:ℝ)*
      (if 3<k then 4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ)) else 0)≤
      if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0 := by
  split_ifs with hk
  · have hcard := cubicThetaIntegerBox_card_bound (show 1≤k by omega)
    have hpow := cubic_nat_fourth_geometric (show 1≤k by omega)
    have hexp := cubic_exp_nat_tail_bound k
    calc
      _ ≤ (9*(k:ℝ)^2)*(4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 36*(k:ℝ)^4*Real.exp (-(241/50:ℝ)*(k:ℝ)) := by ring
      _ ≤ 36*((16:ℝ)^k/16)*(1/120:ℝ)^k := by gcongr
      _ = (9/4:ℝ)*(16*(1/120:ℝ))^k := by rw [mul_pow]; ring
      _ = _ := by norm_num
  · norm_num

lemma cubicThetaRamified_box_geometric (k : ℕ) :
    ((cubicThetaIntegerBox k).card:ℝ)*
      (if 2<k then (k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ)) else 0)≤
      if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0 := by
  split_ifs with hk
  · have hcard := cubicThetaIntegerBox_card_bound (show 1≤k by omega)
    have hpow := cubic_nat_fourth_geometric (show 1≤k by omega)
    have hexp := cubic_exp_nat_high_bound k
    calc
      _ ≤ (9*(k:ℝ)^2)*((k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 9*(k:ℝ)^4*Real.exp (-(6:ℝ)*(k:ℝ)) := by ring
      _ ≤ 9*((16:ℝ)^k/16)*(1/400:ℝ)^k := by gcongr
      _ = (9/16:ℝ)*(16*(1/400:ℝ))^k := by rw [mul_pow]; ring
      _ = _ := by norm_num
  · norm_num

lemma cubicThetaPrimary_far_tail :
    Summable (fun p => if 3<cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) ∧
    (∑' p,if 3<cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0)<1/1000 := by
  let g := fun k : ℕ => if 3<k then 4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ)) else 0
  have hg : ∀ k,0≤g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hb := cubicThetaPrimary_box_geometric
  have hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k) :=
    cubic_primary_geometric_after.1.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (hg k)) hb
  have h := cubicThetaInteger_tsum_bound
    (fun p => if 3<cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) g
    (by
      intro p
      split_ifs
      · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le
      · exact le_rfl) hg
    (by intro p; dsimp [g]; split_ifs with hp
        · exact cubicThetaPrimaryTailMass_bound p (by omega)
        · exact le_rfl) hs
  refine ⟨h.1,h.2.trans_lt ?_⟩
  exact (hs.tsum_le_tsum hb cubic_primary_geometric_after.1).trans_lt cubic_primary_geometric_after.2

lemma cubicThetaRamified_far_tail :
    Summable (fun p => if 2<cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) ∧
    (∑' p,if 2<cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0)<1/10000 := by
  let g := fun k : ℕ => if 2<k then (k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ)) else 0
  have hg : ∀ k,0≤g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hb := cubicThetaRamified_box_geometric
  have hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k) :=
    cubic_ramified_geometric_after.1.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (hg k)) hb
  have h := cubicThetaInteger_tsum_bound
    (fun p => if 2<cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) g
    (by
      intro p
      split_ifs
      · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le
      · exact le_rfl) hg
    (by intro p; dsimp [g]; split_ifs with hp
        · exact cubicThetaRamifiedTailMass_bound p (by omega)
        · exact le_rfl) hs
  refine ⟨h.1,h.2.trans_lt ?_⟩
  exact (hs.tsum_le_tsum hb cubic_ramified_geometric_after.1).trans_lt cubic_ramified_geometric_after.2

end CubicFirstMoment

end

end OAI
