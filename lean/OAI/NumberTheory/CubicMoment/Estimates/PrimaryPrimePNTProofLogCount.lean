import Mathlib

namespace OAI

/-! Unweight a prime logarithmic mean using a moving power cutoff. -/
noncomputable section
open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def selectedRationalPrimes (P : ℕ → Prop) (X : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊X⌋₊).filter P

def selectedRationalTheta (P : ℕ → Prop) (X : ℝ) : ℝ :=
  ∑ p ∈ selectedRationalPrimes P X, Real.log p

def selectedRationalCount (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (selectedRationalPrimes P X).card

lemma selectedRationalTheta_le (P : ℕ → Prop) {X : ℝ} (hX : 1 ≤ X) :
    selectedRationalTheta P X ≤ selectedRationalCount P X * Real.log X := by
  calc
    _ ≤ ∑ _p ∈ selectedRationalPrimes P X, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hp'.2.pos)
        ((Nat.le_floor_iff (by linarith)).mp hp'.1)
    _ = _ := by simp [selectedRationalCount]

lemma selectedRationalCount_upper (P : ℕ → Prop) {X α : ℝ}
    (hX : 1 < X) (hα : 0 < α) :
    selectedRationalCount P X * Real.log X / X ≤
      selectedRationalTheta P X / X / α + (X ^ α + 1) * Real.log X / X := by
  let S := selectedRationalPrimes P X
  let U := S.filter (fun p : ℕ => (p : ℝ) ≤ X ^ α)
  let V := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X ^ α)
  have hY : 0 ≤ X ^ α := Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hX)) _
  have hu : U.card ≤ ⌊X ^ α⌋₊ + 1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊X ^ α⌋₊ + 1)) ?_).trans_eq
      (Finset.card_range _)
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_floor_iff hY).mpr (Finset.mem_filter.mp hp).2))
  have hv : (V.card : ℝ) * (α * Real.log X) ≤ selectedRationalTheta P X := by
    calc
      _ = ∑ _p ∈ V, α * Real.log X := by simp
      _ ≤ ∑ p ∈ V, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hlt := lt_of_not_ge (Finset.mem_filter.mp hp).2
        have hl := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hlt.le
        simpa only [Real.log_rpow (by linarith : (0 : ℝ) < X)] using hl
      _ ≤ selectedRationalTheta P X := by
        change (∑ p ∈ V, Real.log p) ≤ ∑ p ∈ S, Real.log p
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        have hpP := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
        exact Real.log_nonneg (by exact_mod_cast hpP.one_lt.le)
  have hcard : (U.card : ℝ) + V.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S)
      (fun p => (p : ℝ) ≤ X ^ α)
  have hu' : (U.card : ℝ) ≤ X ^ α + 1 := by
    exact (by exact_mod_cast hu : (U.card : ℝ) ≤ ⌊X ^ α⌋₊ + 1).trans
      (by linarith [Nat.floor_le hY])
  have hm : (0 : ℝ) ≤ α * Real.log X := mul_nonneg hα.le (Real.log_nonneg hX.le)
  have hb : selectedRationalCount P X * (α * Real.log X) ≤
      selectedRationalTheta P X + (X ^ α + 1) * (α * Real.log X) := by
    change (S.card : ℝ) * _ ≤ _
    rw [← hcard, add_mul]
    linarith [mul_le_mul_of_nonneg_right hu' hm]
  have hb' := div_le_div_of_nonneg_right hb hα.le
  have heL : selectedRationalCount P X * (α * Real.log X) / α =
      selectedRationalCount P X * Real.log X := by field_simp
  have heR : (selectedRationalTheta P X + (X ^ α + 1) * (α * Real.log X)) / α =
      selectedRationalTheta P X / α + (X ^ α + 1) * Real.log X := by
    field_simp
  rw [heL,heR] at hb'
  have hfinal := div_le_div_of_nonneg_right hb' (show 0 ≤ X by linarith)
  simpa only [add_div, div_right_comm (selectedRationalTheta P X) α X] using hfinal

lemma power_log_remainder_tendsto_zero {α : ℝ} (hα : α < 1) :
    Tendsto (fun X : ℝ => (X ^ α + 1) * Real.log X / X) atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero
  have h2 := (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
  have h := h1.add h2
  norm_num only [Real.rpow_one, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [Real.rpow_sub hX, Real.rpow_one]
  field_simp

/-- A positive logarithmic prime mean gives the ordinary natural-density count. -/
theorem selectedRationalCount_limit (P : ℕ → Prop) {c : ℝ} (hc : 0 < c)
    (hθ : Tendsto (fun X => selectedRationalTheta P X / X) atTop (𝓝 c)) :
    Tendsto (fun X => selectedRationalCount P X * Real.log X / X) atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro d hd
    filter_upwards [hθ.eventually (Ioi_mem_nhds hd), eventually_ge_atTop (1 : ℝ)] with X hXd hX
    exact hXd.trans_le (div_le_div_of_nonneg_right (selectedRationalTheta_le P hX)
      (show 0 ≤ X by linarith))
  · intro d hd
    have hd0 : 0 < d := hc.trans hd
    let α := (c + d) / (2*d)
    have hα0 : 0 < α := by dsimp [α]; positivity
    have hα1 : α < 1 := by
      dsimp [α]
      apply (div_lt_one (by positivity : 0 < 2*d)).mpr
      linarith
    have hcd : c / α < d := by
      apply (div_lt_iff₀ hα0).mpr
      have he : d * α = (c + d) / 2 := by
        dsimp [α]
        field_simp
      rw [he]
      linarith
    have hu := (hθ.div_const α).add (power_log_remainder_tendsto_zero hα1)
    simp only [add_zero] at hu
    filter_upwards [hu.eventually (Iio_mem_nhds hcd), eventually_gt_atTop (1 : ℝ)] with X hXd hX
    exact (selectedRationalCount_upper P hX hα0).trans_lt hXd

end CubicFirstMoment

end

end OAI
