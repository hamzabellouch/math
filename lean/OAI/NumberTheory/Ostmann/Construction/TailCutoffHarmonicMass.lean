import OAI.NumberTheory.Ostmann.Preliminaries.MertensHarmonicBands
import OAI.NumberTheory.Ostmann.Preliminaries.TailCollisionCutoff

namespace OAI

/-! # Harmonic cost of the full ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem MertensHarmonicEstimate.tail_cutoff_mass {C : ℝ} (hM : MertensHarmonicEstimate C)
    (Y L : ℝ) (hY : 1 ≤ Y) (hcut : 2 ≤ Real.exp (Y / 2) / Y ^ 5)
    (hYL : Y ≤ Real.exp L) :
    (∑ p ∈ Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) ≤ L + C := by
  have hY0 : 0 < Y := by linarith
  have hQ2 : 2 ≤ tailCollisionCutoff Y := Nat.le_floor hcut
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast (show 0 < tailCollisionCutoff Y by omega)
  have hQ : (tailCollisionCutoff Y : ℝ) ≤ Real.exp Y := by
    apply (tailCollisionCutoff_bounds Y hY hcut).2.1.trans
    apply (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hY)).trans
    exact Real.exp_le_exp.mpr (by linarith)
  have hlogQ : Real.log (tailCollisionCutoff Y : ℝ) ≤ Y :=
    (Real.log_le_iff_le_exp hQ0).mpr hQ
  have hlogQ0 : 0 < Real.log (tailCollisionCutoff Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < tailCollisionCutoff Y by omega))
  have hlogY : Real.log Y ≤ L := (Real.log_le_iff_le_exp hY0).mpr hYL
  have hh := (abs_le.mp (hM _ hQ2)).2
  have hlogs := Real.log_le_log hlogQ0 hlogQ
  linarith

theorem MertensHarmonicEstimate.tail_cutoff_mass_linear {C : ℝ} (hM : MertensHarmonicEstimate C)
    (Y L : ℝ) (m : ℕ) (hY : 1 ≤ Y) (hcut : 2 ≤ Real.exp (Y / 2) / Y ^ 5)
    (hYL : Y ≤ Real.exp L) (hC : C ≤ L) (hm : L ≤ m) :
    (∑ p : Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) ≤ 2 * m := by
  have hh := hM.tail_cutoff_mass Y L hY hcut hYL
  have he : (∑ p : Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) =
      ∑ p ∈ Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹ := by
    exact Finset.sum_coe_sort (Nat.primesLE (tailCollisionCutoff Y)) (fun p : ℕ => (p : ℝ)⁻¹)
  rw [he]
  linarith

end Ostmann

end OAI
