import OAI.NumberTheory.TotientAsymptotic.FordBandSupports

namespace OAI

/-! The precise normality cap for a band in Ford's iterative count. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandCap (k : ℕ) (y S : ℝ) (Y : ℕ → ℝ) : ℝ :=
  (k:ℝ)*(B (Y (k-1))-B (Y k)+Real.sqrt (B S*B y))

lemma ford_band_omega {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hk : k ≤ b) (hk0 : 1 ≤ k) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    ((pairedProduct (fordBand hk t Y)).primeFactorsList.length:ℝ) ≤ fordBandCap k y S Y := by
  have hkm : k-1 < b := by omega
  have hgap := hp.2.2.2.2.1 (k-1) (Finset.mem_range.mpr hkm)
  have hs := ford_scale_bounds hp
  have hSUk := ford_cutoff_ge_S hp hk
  have hUV : Y k < Y (k-1) := by
    have he : k-1+1=k := by omega
    rw [he] at hgap
    exact hgap.1.trans hgap.2
  have hV1 : 1 < Y (k-1) := (hs.1.trans_le hSUk).trans hUV
  have hVy : Y (k-1) ≤ y := ford_cutoff_le_y hp (by omega)
  have hB : B (Y (k-1)) ≤ B y :=
    Real.log_le_log (Real.log_pos hV1) (Real.log_le_log (by linarith) hVy)
  have hroot : Real.sqrt (B S*B (Y (k-1))) ≤ Real.sqrt (B S*B y) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hB (by linarith [hs.2]))
  have hh := normal_band_product_omega (fun j : Fin k => t.left (Fin.castLE hk j))
    (fun j => (h.2.1 (Fin.castLE hk j)).1) hs.1 (by linarith [hs.2]) hSUk hUV
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hroot) (Nat.cast_nonneg k))

end TotientAsymptotic

end

end OAI
