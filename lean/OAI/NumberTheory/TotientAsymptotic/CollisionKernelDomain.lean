import OAI.NumberTheory.TotientAsymptotic.ActualFordData
import OAI.NumberTheory.TotientAsymptotic.ComparisonClass

namespace OAI

/-! Uniform numerical data for applying the recovered Ford kernel. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma good_residual_omega_floor {x t y : ℝ} {H i : ℕ}
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hi : i ≤ R x H) (hq : GoodCollisionBlock x t H i y q) :
    (collisionResidual (chosenRemainder x H q.1.tail) i).primeFactorsList.length ≤
      ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ ∧
    (collisionResidual (chosenRemainder x H q.2.tail) i).primeFactorsList.length ≤
      ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ := by
  have hm := Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩
  constructor
  · exact Nat.le_floor ((chosenRemainder_good hq.left i hm).2.2.2)
  · exact Nat.le_floor ((chosenRemainder_good hq.right i hm).2.2.2)

lemma normalized_grid_bottom {b : ℕ} {y Z δ : ℝ} (v : Fin b → ℕ)
    (hb : 0 < b) (hy : B y ≠ 0) :
    B (comparisonCutoffs y (pairedGridUpper δ ((7/10 : ℝ)*Z/B y) v) b)=(7/10 : ℝ)*Z := by
  rw [B,comparisonCutoffs,Real.log_exp,Real.log_exp]
  simp only [pairedGridUpper,ite_eq_right (Nat.ne_of_gt hb),lt_self_iff_false,dite_false]
  field_simp

lemma comparison_cutoff_one_lt (y : ℝ) (v : ℕ → ℝ) (b : ℕ) :
    1 < comparisonCutoffs y v b := Real.one_lt_exp_iff.mpr (Real.exp_pos _)

/-- All scalar hypotheses of the single-class kernel follow uniformly from
the Ford bands. The only tuple-dependent bound is its number of survivors. -/
theorem collision_kernel_domain : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    5 ≤ ((m x-i : ℕ) : ℝ) ∧ 1 ≤ Real.log y ∧
    ((R x H-collisionLastIndex x i : ℕ) : ℝ) ≤ ((m x-i : ℕ) : ℝ) ∧
    Real.log (B y) ≤ 26*((m x-i : ℕ) : ℝ) ∧
    (⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ : ℝ) ≤
      2*B y/((m x-i : ℕ) : ℝ)^8 ∧
    0 < fordBandScale x (collisionLastIndex x i) ∧
    (7/10 : ℝ)*fordBandScale x (collisionLastIndex x i) ≤
      2*B y/((m x-i : ℕ) : ℝ)^18 ∧
    collisionCutoff (m x-i)+1 ≤ m x-i := by
  filter_upwards [eventually_collision_indices,ford_band_polynomial_lower 1,
    eventually_ge_atTop 5] with H hind hpoly hH
  filter_upwards [hpoly,ford_band_log_upper,
    m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hp hl hm hBx
  intro i hi hL hR y hy hBy hlo hup
  have him : i < m x := hi.trans_lt (hR.trans hL)
  obtain ⟨hHi,hcut,hk⟩ := hind x hm i hi
  have hh : (5 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := by linarith
  have hbi : 0 < fordBandScale x i := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hbige : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hp i him hHi
  have hBy1 : 1 ≤ B y := by
    have hh5 : (5 : ℝ) ≤ fordBandScale x i := hh.trans hbige
    linarith
  have hlogy : 1 ≤ Real.log y := by
    have he := Real.exp_le_exp.mpr hBy1
    rw [B,Real.exp_log (Real.log_pos hy)] at he
    have he1 := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hn : R x H-collisionLastIndex x i ≤ m x-i := by
    have hkge : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
    omega
  have hlog := (Real.log_le_log hBy (show B y ≤ 6*fordBandScale x i by linarith)).trans (hl i him)
  have hf := Nat.floor_le (div_nonneg hbi.le (pow_nonneg hh0.le 8))
  have hratio := (ford_collision_layer_ratio hBx him hcut).2
  have hZ : 0 < fordBandScale x (collisionLastIndex x i) :=
    fordBandScale_pos (zero_lt_one.trans hBx) (hk.trans hL)
  have hzu : fordBandScale x (collisionLastIndex x i) ≤
      fordBandScale x i/((m x-i : ℕ) : ℝ)^18 := by
    have ht := (div_le_iff₀ hbi).mp hratio
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using ht
  refine ⟨hh,hlogy,by exact_mod_cast hn,hlog,?_,hZ,?_,by omega⟩
  · apply hf.trans
    apply div_le_div_of_nonneg_right _ (pow_nonneg hh0.le _)
    linarith
  · have hdiv := div_le_div_of_nonneg_right
      (show (7/10 : ℝ)*fordBandScale x i ≤ 2*B y by linarith)
      (pow_nonneg hh0.le 18)
    have hz := mul_le_mul_of_nonneg_left hzu (by norm_num : (0 : ℝ) ≤ 7/10)
    exact hz.trans (by simpa only [mul_div_assoc] using hdiv)

end TotientAsymptotic

end

end OAI
