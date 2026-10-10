import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayLinear

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positiveDivisorArray_norm_polynomial {L Z s P : ℕ}
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hs : 0 < s) (hP : 0 < P)
    (q : ℕ) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    ‖positiveDivisorArray L q lam A mInv P R h θ s‖ ≤ cutoffFourierBound*(Z:ℝ)^3 := by
  have hG : ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ (Z:ℝ)*cutoffFourierBound := by
    intro d hd v hv
    have hdsq := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    have hh := divisorQuadraticSumP_norm_le hdsq A (mInv d) hs (Nat.pos_of_mem_divisors hv) P hR h θ
    have hsqrt : Real.sqrt (d:ℝ) ≤ (Z:ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity,?_⟩
      have hdz : (d:ℝ) ≤ Z := by exact_mod_cast (Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd)).trans hLZ
      have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
      nlinarith
    calc
      _ ≤ Real.sqrt (d:ℝ)*cutoffFourierBound/P := hh
      _ ≤ Real.sqrt (d:ℝ)*cutoffFourierBound :=
        div_le_self (by have := cutoffFourierBound_pos; positivity) (by exact_mod_cast hP)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt cutoffFourierBound_pos.le
  rw [positiveDivisorArray_eq_linear]
  have hh := adaptiveArrayLinear_norm_le L q hlam hs _
    (show 0 ≤ (Z:ℝ)*cutoffFourierBound by have := cutoffFourierBound_pos; positivity) hG
  have hc : (L.divisors.card:ℝ) ≤ Z := by exact_mod_cast (Nat.card_divisors_le_self L).trans hLZ
  calc
    _ ≤ (L.divisors.card:ℝ)^2*((Z:ℝ)*cutoffFourierBound) := hh
    _ ≤ (Z:ℝ)^2*((Z:ℝ)*cutoffFourierBound) := by
      have := cutoffFourierBound_pos
      have := adaptiveArrayConstant_pos
      gcongr
    _ = _ := by ring

theorem positiveDivisorArray_grid_error {L Z s : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hs : 0 < s) (hsZ : s ≤ Z^14)
    (q P : ℕ) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R R' θ θ' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R')
    (hRB : R ≤ (2*Z^13:ℕ)) (hRB' : R' ≤ (2*Z^13:ℕ)) (h : ℝ)
    (ht : |θ-θ'| ≤ 1/(Z^200:ℕ)) (hr : |R-R'| ≤ 1/(Z^200:ℕ)) :
    ‖positiveDivisorArray L q lam A mInv P R h θ s-
      positiveDivisorArray L q lam A mInv P R' h θ' s‖ ≤
      adaptiveArrayConstant*(Z:ℝ)^48/(Z^200:ℕ) := by
  rw [positiveDivisorArray_eq_linear,positiveDivisorArray_eq_linear,adaptiveArrayLinear_sub]
  have hG : ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (mInv d) s v P R h θ-
        divisorQuadraticSumP d A (mInv d) s v P R' h θ'‖ ≤
        adaptiveArrayConstant*(Z:ℝ)^46/(Z^200:ℕ) := by
    intro d hd v hv
    exact divisorQuadraticSumP_grid_error hZ
      (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)) hs (Nat.pos_of_mem_divisors hv)
      ((Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd)).trans hLZ) ((Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hv)).trans hLZ)
      hsZ A (mInv d) P hR hR' hRB hRB' h ht hr
  have hh := adaptiveArrayLinear_norm_le L q hlam hs _
    (show 0 ≤ adaptiveArrayConstant*(Z:ℝ)^46/(Z^200:ℕ) by have := adaptiveArrayConstant_pos; positivity) hG
  have hc : (L.divisors.card:ℝ) ≤ Z := by exact_mod_cast (Nat.card_divisors_le_self L).trans hLZ
  calc
    _ ≤ (L.divisors.card:ℝ)^2*(adaptiveArrayConstant*(Z:ℝ)^46/(Z^200:ℕ)) := hh
    _ ≤ (Z:ℝ)^2*(adaptiveArrayConstant*(Z:ℝ)^46/(Z^200:ℕ)) := by
      have := cutoffFourierBound_pos
      have := adaptiveArrayConstant_pos
      gcongr
    _ = _ := by ring

end Ostmann.QuadraticCenter

end

end OAI
