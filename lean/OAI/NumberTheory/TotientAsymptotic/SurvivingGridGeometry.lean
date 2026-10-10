import OAI.NumberTheory.TotientAsymptotic.CollisionFactorHeights
import OAI.NumberTheory.TotientAsymptotic.PairedComparisonGrid

namespace OAI

/-! Numerical grid margins for the ordered surviving Ford bands. -/

noncomputable section

namespace TotientAsymptotic

lemma collision_last_band_le_half {x : ℝ} {i : ℕ} (hB : 1<B x) (hi : i < m x)
    (hh : 2 ≤ m x-i) (hcut : 2*collisionCutoff (m x-i)< m x-i) :
    fordBandScale x (collisionLastIndex x i) ≤ fordBandScale x i/2 := by
  have hb := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hp : (2 : ℝ) ≤ ((m x-i : ℕ) : ℝ)^18 := by
    have h2 : (2 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hh
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) h2 18
    norm_num at hp
    linarith
  have hr := (div_le_iff₀ hb).mp (ford_collision_layer_ratio hB hi hcut).2
  have hfrac : 1/((m x-i : ℕ) : ℝ)^18 ≤ (1/2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  exact hr.trans (by nlinarith)

/-- This statement concerns the actual band heights only; the finite grid
rounding is added afterwards. The first height uses the large head-prime
bound, and every other height uses its own Ford band. -/
theorem ordered_surviving_band_margins {x Y : ℝ} {i k b : ℕ}
    (hb : 0<b) (hB : 1<B x) (hi : i < m x) (hk : k < m x)
    (j : Fin b ↪o ℕ) (hj0 : j ⟨0,hb⟩=i) (hjk : ∀ r, j r≤k)
    (_hY : 0<Y) (hYl : (87/100 : ℝ)*fordBandScale x i≤Y)
    (hlast : fordBandScale x k ≤ fordBandScale x i/2)
    (u v : Fin b → ℝ)
    (hhead : (9/10 : ℝ)*Y≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩))
    (hlo : ∀ r, 0<r.val → (22/25 : ℝ)*fordBandScale x (j r)≤ min (u r) (v r))
    (hhi : ∀ r, 0<r.val → max (u r) (v r)≤(28/25 : ℝ)*fordBandScale x (j r)) :
    (∀ r, 0<r.val → max (u r) (v r)≤(18/25 : ℝ)*Y) ∧
    (∀ r, (4/5 : ℝ)*fordBandScale x k≤ min (u r) (v r)) ∧
    (∀ r s, r<s → (1/10 : ℝ)*fordBandScale x k≤ min (u r) (v r)-max (u s) (v s)) := by
  have hbi := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hbk := fordBandScale_pos (zero_lt_one.trans hB) hk
  have htail (r : Fin b) (hr : 0<r.val) :
      max (u r) (v r)≤(28/25 : ℝ)*rho*fordBandScale x i := by
    have hir : i<j r := by
      rw [← hj0]
      exact j.strictMono hr
    have hs := ford_band_step hB hir ((hjk r).trans_lt hk)
    exact (hhi r hr).trans (by nlinarith)
  constructor
  · intro r hr
    have hh := htail r hr
    have hρ := mul_lt_mul_of_pos_right collision_rho_bounds.2 hbi
    nlinarith
  constructor
  · intro r
    by_cases hr : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr
      subst r
      nlinarith
    · have hm := ford_band_antitone hB (hjk r) hk
      have hl := hlo r (by omega)
      nlinarith
  · intro r s hrs
    have hs0 : 0<s.val := by have h0 : (0 : ℕ) ≤ r.val := Nat.zero_le _; exact h0.trans_lt hrs
    by_cases hr : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr
      subst r
      have ht := htail s hs0
      have hρ := mul_lt_mul_of_pos_right collision_rho_bounds.2 hbi
      nlinarith
    · have hg := normal_factor_band_gap hB (j.strictMono hrs) (hjk s) hk
        (hlo r (by omega)) (hhi s hs0)
      linarith

end TotientAsymptotic

end

end OAI
