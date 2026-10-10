import OAI.NumberTheory.Catalan.Analysis.RealPlaceLimsup
import OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceAssembly
import OAI.NumberTheory.Catalan.Polynomial.Rationality

namespace OAI


noncomputable section

namespace InternalCatalan

open Filter

theorem determinantRat_finite_place_liminf (z : ℚ) (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) (hne : ∀ k, determinantRat z (s k) ≠ 0) :
    ((-(8609 / 4608 : ℝ) -
      ((1 / 2 : ℝ) + 505 / 4608) * Real.log 2 : ℝ) : EReal) ≤
      Filter.liminf (fun k =>
        manuscriptNormalizedLogSize (s k) (determinantRat z (s k) : ℝ)) atTop := by
  refine (Filter.le_liminf_iff').2 ?_
  intro y hy
  obtain ⟨r, hyr, hrc⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hr : r < finiteLowerConstant := EReal.coe_lt_coe_iff.mp hrc
  have hε : 0 < finiteLowerConstant - r := sub_pos.mpr hr
  filter_upwards [hs.eventually
    (determinantRat_finite_place_eventually_lower z hε)] with k hk
  have hneR : (determinantRat z (s k) : ℝ) ≠ 0 := by exact_mod_cast hne k
  rw [manuscriptNormalizedLogSize_of_ne_zero hneR]
  refine hyr.le.trans (EReal.coe_le_coe_iff.mpr ?_)
  have hb := hk (hne k)
  dsimp [finiteLowerConstant] at hb
  linarith

theorem determinant_finite_place_liminf {z : ℚ} (hz : (z : ℝ) = catalan)
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (hne : ∀ k, determinantRat z (s k) ≠ 0) :
    ((-(8609 / 4608 : ℝ) -
      ((1 / 2 : ℝ) + 505 / 4608) * Real.log 2 : ℝ) : EReal) ≤
      Filter.liminf (fun k => manuscriptDeterminantLogSize (s k)) atTop := by
  have heq : (fun k => manuscriptNormalizedLogSize (s k)
      (determinantRat z (s k) : ℝ)) =ᶠ[atTop]
      (fun k => manuscriptDeterminantLogSize (s k)) := by
    filter_upwards [hs.eventually (eventually_ge_atTop (1 : ℕ))] with k hk
    have hpos : 0 < s k := lt_of_lt_of_le Nat.zero_lt_one hk
    simp only [manuscriptDeterminantLogSize, determinantRat_cast hz hpos]
  rw [← Filter.liminf_congr heq]
  exact determinantRat_finite_place_liminf z s hs hne

theorem determinant_finite_place_liminf_of_nonzero {z : ℚ}
    (hz : (z : ℝ) = catalan) (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (hne : ∀ k, determinant (s k) ≠ 0) :
    ((-(8609 / 4608 : ℝ) -
      ((1 / 2 : ℝ) + 505 / 4608) * Real.log 2 : ℝ) : EReal) ≤
      Filter.liminf (fun k => manuscriptDeterminantLogSize (s k)) atTop := by
  refine (Filter.le_liminf_iff').2 ?_
  intro y hy
  obtain ⟨r, hyr, hrc⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hr : r < finiteLowerConstant := EReal.coe_lt_coe_iff.mp hrc
  have hε : 0 < finiteLowerConstant - r := sub_pos.mpr hr
  filter_upwards [hs.eventually (determinantRat_finite_place_eventually_lower z hε),
    hs.eventually (eventually_ge_atTop (1 : ℕ))] with k hk hpos
  have hsk : 0 < s k := lt_of_lt_of_le Nat.zero_lt_one hpos
  have hnrat := (determinantRat_ne_zero_iff hz hsk).mpr (hne k)
  have hb := hk hnrat
  rw [determinantRat_cast hz hsk] at hb
  rw [manuscriptDeterminantLogSize_of_ne_zero (hne k)]
  refine hyr.le.trans (EReal.coe_le_coe_iff.mpr ?_)
  dsimp [finiteLowerConstant] at hb
  linarith

theorem finite_place_liminf_constant_gt_threshold :
    ((-(229084 / 100000 : ℝ)) : EReal) <
      ((-(8609 / 4608 : ℝ) -
        ((1 / 2 : ℝ) + 505 / 4608) * Real.log 2 : ℝ) : EReal) :=
  EReal.coe_lt_coe_iff.mpr finitePlace_constant_gt_threshold

end InternalCatalan

end

end OAI
