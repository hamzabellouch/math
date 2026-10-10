import OAI.MeasureTheory.Falconer.Shells.RestorationSubpower

namespace OAI

namespace PlanarFalconer
open scoped ENNReal

theorem restoration_power_rate (H₁ H₂ : ℕ) {lam sig p q : ℝ}
    (hlam : 0 < lam) (hsig : 0 < sig) (hpq : p.HolderConjugate q) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C K : ENNReal,
      C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p)) ≤
      (C*(4+2*K))*ENNReal.ofReal (((2:ℝ)^N)^(-eta)) := by
  have ha : 0 < 1-1/p := by
    have hh := hpq.one_div_add_one_div
    have hq := one_div_pos.mpr hpq.symm.pos
    linarith
  let eta := min 2 (min (lam/2) ((lam+sig)*(1-1/p)/2))
  have heta : 0 < eta := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨N₁,h₁⟩ := restorationDiscardBound_decay H₁ hlam
  obtain ⟨N₂,h₂⟩ := restorationDiscardBound_decay H₂ hlam
  obtain ⟨N₃,h₃⟩ := restorationArcBound_decay H₁ (add_pos hlam hsig)
  obtain ⟨N₄,h₄⟩ := restorationArcBound_decay H₂ (add_pos hlam hsig)
  refine ⟨eta,heta,max (max N₁ N₂) (max N₃ N₄),?_⟩
  intro N hN C K
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₄ : N₄ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let Z := ENNReal.ofReal (((2:ℝ)^N)^(-eta))
  have hpow (e : ℝ) (he : eta ≤ e) : ENNReal.ofReal (((2:ℝ)^N)^(-e)) ≤ Z :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (neg_le_neg he))
  have h2 := hpow 2 (min_le_left _ _)
  have hl := hpow (lam/2) ((min_le_right _ _).trans (min_le_left _ _))
  have harc : (ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)/2)))^(1-1/p) ≤ Z := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ha.le,← Real.rpow_mul (by positivity)]
    have he : -(lam+sig)/2*(1-1/p) = -((lam+sig)*(1-1/p)/2) := by ring
    rw [he]
    exact hpow _ ((min_le_right _ _).trans (min_le_right _ _))
  have hd₁ : restorationDiscardBound N H₁ lam ≤ Z+Z := by
    apply (h₁ N hN₁).trans
    simpa only [neg_div] using add_le_add h2 hl
  have hd₂ : restorationDiscardBound N H₂ lam ≤ Z+Z := by
    apply (h₂ N hN₂).trans
    simpa only [neg_div] using add_le_add h2 hl
  have hw₁ : (restorationArcBound N H₁ lam sig)^(1-1/p) ≤ Z :=
    (ENNReal.rpow_le_rpow (h₃ N hN₃) ha.le).trans harc
  have hw₂ : (restorationArcBound N H₂ lam sig)^(1-1/p) ≤ Z :=
    (ENNReal.rpow_le_rpow (h₄ N hN₄) ha.le).trans harc
  calc
    _ ≤ C*((Z+Z)+(Z+Z)+K*Z+K*Z) := by gcongr
    _ = (C*(4+2*K))*Z := by ring

end PlanarFalconer

end OAI
