import OAI.NumberTheory.TotientAsymptotic.CollisionGrid
import OAI.NumberTheory.TotientAsymptotic.CollisionGridScale
import OAI.NumberTheory.TotientAsymptotic.CollisionLogBudget

namespace OAI

/-! The complete family of alignment grids has only exponential-square cost. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collisionMesh_inverse_bound {x y : ℝ} {i : ℕ}
    (hS : 1 ≤ B (normalityScale x i)) (hy : 1 ≤ B y) :
    1/collisionMesh x y i ≤ B y := by
  have hmul : 1 ≤ B (normalityScale x i)*B y := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (B (normalityScale x i)*B y) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmul
  rw [collisionMesh,one_div_div]
  exact div_le_self (zero_le_one.trans hy) hsqrt

lemma alignment_grid_card_bound {x y : ℝ} {i b h : ℕ}
    (hS : 1 ≤ B (normalityScale x i)) (hy : 1 ≤ B y)
    (hbh : b ≤ h) (hlog : Real.log (2*B y) ≤ 26*h) :
    ((collisionGridFamilies (collisionMesh x y i) b).card : ℝ) ≤
      Real.exp (26*(h : ℝ)^2) := by
  rw [collisionGridFamilies_card,Nat.cast_pow]
  have hbase : ((⌊1/collisionMesh x y i⌋₊+1 : ℕ) : ℝ) ≤ 2*B y := by
    have hδ : 0 < collisionMesh x y i := by
      unfold collisionMesh
      exact div_pos (Real.sqrt_pos.mpr (by nlinarith)) (zero_lt_one.trans_le hy)
    have hf := Nat.floor_le (show 0 ≤ 1/collisionMesh x y i by positivity)
    have hb := collisionMesh_inverse_bound hS hy
    push_cast
    linarith
  have hp : 0 < 2*B y := by linarith
  calc
    _ ≤ (2*B y)^b := pow_le_pow_left₀ (by positivity) hbase b
    _ = Real.exp ((b : ℝ)*Real.log (2*B y)) := by rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hbR : (b : ℝ) ≤ h := by exact_mod_cast hbh
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      have hm := mul_le_mul hlog hbR (Nat.cast_nonneg b) (by positivity : (0 : ℝ) ≤ 26*h)
      nlinarith

/-- The source's grid-choice cost is bounded uniformly in the phase by
`exp (26 h²)` for all retained positive or zero collision indices. -/
theorem collision_grid_card_uniform : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 ≤ B (normalityScale x i) → 1 ≤ B y →
    B y ≤ 2*fordBandScale x i → ∀ b ≤ m x-i,
    ((collisionGridFamilies (collisionMesh x y i) b).card : ℝ) ≤
      Real.exp (26*((m x-i : ℕ) : ℝ)^2) := by
  filter_upwards [eventually_ge_atTop 1] with H hH
  filter_upwards [ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hS hy hBy b hb
  have him : i < m x := by unfold R at hi; omega
  apply alignment_grid_card_bound hS hy hb
  have hp : 0 < 2*B y := by linarith
  have hb0 : 0 < fordBandScale x i := by linarith
  exact (Real.log_le_log hp (show 2*B y ≤ 6*fordBandScale x i by linarith)).trans (hx i him)

end TotientAsymptotic

end

end OAI
