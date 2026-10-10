import OAI.NumberTheory.Jacobsthal.Estimates.ActualUnalignedIncidence
import OAI.NumberTheory.Jacobsthal.Partitions.BoxInflation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosInverseBoxHeight

noncomputable def ignoredPrimes (P : Finset ℕ) (d : ℕ) : Finset ℕ := by
  classical
  exact P.filter (fun p => p ∣ d)

theorem ignoredPrimes_card_le (P : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P,Nat.Prime p) (z alpha : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hheight : (d : ℝ) ≤ z) :
    ((ignoredPrimes P d).card : ℝ) ≤ 1/alpha := by
  have he : ignoredPrimes P d = dividingPrimes P (d : ℤ) := by
    classical
    ext p
    simp only [ignoredPrimes,dividingPrimes,Finset.mem_filter,Int.natCast_dvd_natCast]
  rw [he]
  apply dividingPrimes_card_bound P (d : ℤ) (by exact_mod_cast hd.ne') hP z alpha 1 hz ha hlarge
  simpa only [Int.cast_natCast,abs_of_nonneg (show (0 : ℝ) ≤ d from Nat.cast_nonneg d),Real.rpow_one] using hheight

theorem source_denominator_le_z {z R Z d : ℝ} (hz : 1 < z) (_hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hd : d ≤ R*Z^10) : d ≤ z := by
  have hz0 : 0 < z := by linarith
  have hZ10 : Z^10 ≤ z^((10 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^10 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  calc
    d ≤ R*Z^10 := hd
    _ ≤ z^((1 : ℝ)/100)*z^((10 : ℝ)/100) := by gcongr
    _ = z^((11 : ℝ)/100) := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ z := by
      have hh := Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (11 : ℝ)/100 ≤ 1)
      simpa only [Real.rpow_one] using hh

end ErdosSourceCollision

end

end Erdos970

end OAI
