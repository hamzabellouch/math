import OAI.NumberTheory.TotientAsymptotic.CollisionLogBudget
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-! Separated largest-factor bands for the actual normal remainder primes. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma basic_remainder_prime_ge_three {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hj : j ∈ Finset.Icc 1 (L x H)) (hjm : j < m x) : 3 ≤ remainderPrime η j := by
  have hp := hη.2.1 j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hpos : 0 < B (remainderPrime η j) := by
    have hh := mul_pos (by norm_num : (0 : ℝ) < 9/10) (bandScale_pos hjm)
    have hlo : (9/10 : ℝ)*bandScale x j ≤ B (remainderPrime η j) := by
      simpa only [remainderCoord,B,ite_eq_right hj0] using hp.2.1
    exact hh.trans_le hlo
  by_contra! hn
  have he : remainderPrime η j=2 := by have := hp.1.two_le; omega
  rw [he] at hpos
  norm_num only [Nat.cast_ofNat] at hpos
  have hlog : Real.log (Real.log (2 : ℝ)) < 0 := Real.log_neg
    (Real.log_pos (by norm_num)) (lt_trans Real.log_two_lt_d9 (by norm_num))
  exact (not_lt_of_ge hpos.le) hlog

lemma normal_remainder_largest_band {x S y : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hj : j ∈ Finset.Icc 1 (L x H)) (hjm : j < m x)
    (hp : IsNormalPrime S (remainderPrime η j)) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSy : S ≤ y) (hBy : 0 < B y)
    (hpy : (remainderPrime η j-1 : ℕ) ≤ y)
    (hloss : 1+Real.log (3*B y) ≤ (1/100 : ℝ)*bandScale x j) :
    (89/100 : ℝ)*bandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (11/10 : ℝ)*bandScale x j := by
  have hp3 := basic_remainder_prime_ge_three hη hj hjm
  have hp1 : (1 : ℝ) < (remainderPrime η j-1 : ℕ) := by exact_mod_cast (show 2 ≤ remainderPrime η j-1 by omega)
  have hSb := Real.log_le_log (Real.log_pos hS) (Real.log_le_log (zero_lt_one.trans hS) hSy)
  have hpb := Real.log_le_log (Real.log_pos hp1) (Real.log_le_log (zero_lt_one.trans hp1) hpy)
  have hh := hη.2.1 j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hu : (9/10 : ℝ)*bandScale x j ≤ B (remainderPrime η j) ∧
      B (remainderPrime η j) ≤ (11/10 : ℝ)*bandScale x j := by
    simpa only [remainderCoord,B,ite_eq_right hj0] using hh.2
  have hn := normal_prime_largest_band hp hp3 hS hBS hSb hBy hpb hu.1 hu.2
  change (9/10 : ℝ)*bandScale x j-1-Real.log (3*B y) ≤
    B (largestPrimeFactor (remainderPrime η j-1)) ∧ _ at hn
  exact ⟨by linarith [hn.1],hn.2⟩

/-- Uniformly over the whole collision block, the normality error is absorbed
by one percent of each actual prime band. -/
theorem collision_normal_factor_bands : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ j ∈ Finset.Icc 1 (collisionLastIndex x i), j ≤ L x H →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    IsNormalPrime (normalityScale x i) (remainderPrime η j) →
    (remainderPrime η j-1 : ℕ) ≤ y →
    (89/100 : ℝ)*bandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (11/10 : ℝ)*bandScale x j := by
  filter_upwards [collision_log_loss_small,eventually_collision_indices] with H hlog hind
  filter_upwards [hlog,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi j hj hjL η hη y hS hBS hSy hBy hByu hnorm hpy
  have hk := (hind x hm i hi).2.2
  have hjm : j < m x := by
    exact ((Finset.mem_Icc.mp hj).2.trans_lt hk).trans_le (Nat.sub_le _ _)
  apply normal_remainder_largest_band hη (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,hjL⟩)
    hjm hnorm hS hBS hSy hBy hpy
  exact (hx i hi y hBy hByu).trans (mul_le_mul_of_nonneg_left
    (bandScale_antitone x (Finset.mem_Icc.mp hj).2) (by norm_num))

lemma separated_normal_factor_bands {x : ℝ} {j k : ℕ} (hjk : j < k) (hjm : j < m x) :
    (11/10 : ℝ)*bandScale x k < (89/100 : ℝ)*bandScale x j := by
  have hh := (bandScale_antitone x (show j+1 ≤ k by omega)).trans (bandScale_succ_le x j)
  have hp := bandScale_pos hjm
  nlinarith [collision_rho_bounds.2]

end TotientAsymptotic

end

end OAI
