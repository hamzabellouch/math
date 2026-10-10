import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RootMomentCauchyBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma cell_reciprocal_bounds {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    1/a ≤ m ∧ 1/a^2 ≤ m := by
  by_cases ha1 : 1 ≤ a
  · have h2 : 1 ≤ a^2 := by nlinarith
    exact ⟨(div_le_one ha).mpr ha1 |>.trans hm,
      (div_le_one (sq_pos_of_pos ha)).mpr h2 |>.trans hm⟩
  · have ha1 : a ≤ 1 := le_of_not_ge ha1
    have h2 : a^2 ≤ a := by nlinarith
    have h32 : a^3 ≤ a^2 := by nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]
    exact ⟨(one_div_le_one_div_of_le (pow_pos ha 3) (le_trans h32 h2)).trans h3,
      (one_div_le_one_div_of_le (pow_pos ha 3) h32).trans h3⟩

lemma cell_mass_product {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    1 ≤ a*m := by
  have hh := (cell_reciprocal_bounds ha hm h3).1
  exact (div_le_iff₀ ha).mp hh |>.trans_eq (by ring)

lemma localOffsetMass_cube_le (D : ℝ) (y : Space) :
    1/(localCellRadius y)^3 ≤ localOffsetMass D y := by
  unfold localOffsetMass
  linarith [le_max_left (1/localCellRadius y^3) 1, Real.sqrt_nonneg (D*localCellRadius y)]

lemma localOffsetMass_offset {D : ℝ} (hD : 0 ≤ D) {y : Space} (hy : y ≠ 0) :
    D*localCellRadius y ≤ (localOffsetMass D y)^2 := by
  have ha := localCellRadius_pos hy
  have h0 : 0 ≤ max (1/localCellRadius y^3) 1 := le_trans zero_le_one (le_max_right _ _)
  have hs := Real.sq_sqrt (mul_nonneg hD ha.le)
  have hn := Real.sqrt_nonneg (D*localCellRadius y)
  unfold localOffsetMass
  nlinarith

lemma cell_four_thirds_bound {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    m^(4/3:ℝ) ≤ a*m^2 := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have ham : 1 ≤ a^3*m := by
    have := (div_le_iff₀ (pow_pos ha 3)).mp h3
    nlinarith
  have ham2 : 1 ≤ a^3*m^2 := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg ha.le 3) hm0)
    nlinarith
  have hp : (m^(4/3:ℝ))^3 = m^4 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hm0]
    norm_num
  have hh := mul_le_mul_of_nonneg_right ham2 (show 0 ≤ m^4 by positivity)
  have hpow : (m^(4/3:ℝ))^3 ≤ (a*m^2)^3 := by rw [hp]; nlinarith
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hm0 _) (by positivity : 0 ≤ a*m^2) (by decide : (3:ℕ) ≠ 0)).mp hpow

end CoulombAtom

end

end OAI
