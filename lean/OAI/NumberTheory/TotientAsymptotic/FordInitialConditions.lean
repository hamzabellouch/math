import OAI.NumberTheory.TotientAsymptotic.FordInitialFactor

namespace OAI

/-! The generic rough-factor count applies to the first factor of a Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_initial_conditions {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hy : 0 ≤ y) (hBy : 1 ≤ B y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    InitialRoughConditions
      (partBelow (t.left ⟨0,by have := hp.1; omega⟩-1) (Y 1))
      (partBelow (t.right ⟨0,by have := hp.1; omega⟩-1) (Y 1))
      (D*r*factorProduct (fordFactorState t (Y 1))) y (Y 1) (fordInitialFactor hp.1 t Y) := by
  let n := fordInitialFactor hp.1 t Y
  let f := fordBand hp.1 t Y
  have hl : f.1 0=n := by simpa only [pairedProduct,Fin.prod_univ_one] using ford_initial_band hp h
  have hr : f.2 0=n := by
    have he : f.1 0=f.2 0 := by
      simpa only [pairedProduct,Fin.prod_univ_one] using ford_band_product_eq hp.1 hp h
    exact he.symm.trans hl
  have hw : CollisionBandConditions
      (partBelow (t.left ⟨0,by have := hp.1; omega⟩-1) (Y 1))
      (partBelow (t.right ⟨0,by have := hp.1; omega⟩-1) (Y 1))
      (0:Fin 1) y (U 0) (Y 1) (Y 0) (fordBandCap 1 y S Y) f :=
    ford_band_conditions hp.1 (0:Fin 1) (by decide) hy hp h
  have hS := ford_scale_bounds hp
  have hSy : S ≤ y := by
    simpa only [hp.2.1] using ford_cutoff_ge_S hp (j:=0) (Nat.zero_le b)
  have hBSy : B S ≤ B y := Real.log_le_log (Real.log_pos hS.1)
    (Real.log_le_log (by linarith) hSy)
  have hSY₁ := ford_cutoff_ge_S hp hp.1
  have hBSY : B S ≤ B (Y 1) := Real.log_le_log (Real.log_pos hS.1)
    (Real.log_le_log (by linarith) hSY₁)
  have hroot : Real.sqrt (B S*B y) ≤ B y := Real.sqrt_le_iff.mpr
    ⟨by linarith,by nlinarith [mul_le_mul_of_nonneg_right hBSy (by linarith : 0 ≤ B y)]⟩
  have hΩ := ford_band_omega hp.1 (by decide) hp h
  rw [ford_initial_band hp h] at hΩ
  have hcap : fordBandCap 1 y S Y ≤ 3*B y := by
    dsimp [fordBandCap]
    simp only [hp.2.1,Nat.cast_one,one_mul]
    linarith [hS.2]
  have hsize : ((D*shiftedProduct t.left:ℕ):ℝ)*(r:ℝ) ≤ y := by
    have hr0 : (0:ℝ) < r := by
      rcases hp with ⟨_,_,_,_,_,_,_,_,_,_,hrNat,_⟩
      exact_mod_cast hrNat
    exact (le_div_iff₀ hr0).mp h.2.2.2.1
  rw [← ford_initial_decomposition hp h] at hsize
  constructor
  · simpa only [ford_initial_band hp h] using ford_band_squarefree hp.1 hp h
  · exact h.2.2.2.2.2.1 (by have := hp.1; omega)
  · convert hsize using 1
    push_cast
    ring
  · simpa only [hl] using hw.left_prime
  · simpa only [hr] using hw.right_prime
  · simpa only [hl,hr] using hw.different
  · simpa only [hl] using hw.left_le
  · simpa only [hr] using hw.right_le
  · exact hΩ.trans hcap
  · intro p hpn
    have hprod : pairedProduct f = fordInitialFactor hp.1 t Y := ford_initial_band hp h
    have hh := hw.support p (by rw [hprod]; exact hpn)
    simpa only [hp.2.1] using hh

end TotientAsymptotic

end

end OAI
