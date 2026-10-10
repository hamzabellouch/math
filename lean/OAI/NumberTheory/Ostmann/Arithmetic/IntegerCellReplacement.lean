import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellLog
import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators
open Set MeasureTheory

def integerDensityMass (M : ℕ) (lo hi G : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ t in lo..hi, Real.exp (t-G)*φ (t-G))/(M : ℝ)

theorem integerResidueMass_error (N M : ℕ) [NeZero M] (a : ZMod M)
    (φ ψ : ℝ → ℝ) (G lo hi B D : ℝ) (hlohi : lo ≤ hi)
    (hN : ⌊Real.exp hi⌋₊ ≤ N)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Continuous ψ)
    (hB : ∀ t ∈ Icc lo hi, |φ (t-G)| ≤ B)
    (hD : ∀ t ∈ Icc lo hi, |ψ (t-G)| ≤ D) :
    |integerResidueMass N M a lo hi G φ-integerDensityMass M lo hi G φ| ≤
      Real.exp (-G)*(5*B+2*D*(hi-lo)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB lo ⟨le_rfl, hlohi⟩)
  have he := closed_endpoint_error N M a lo hi hN (fun n => φ (Real.log n-G)) hB0
    (fun n hn => by
      have hs := (Finset.mem_filter.mp hn).2
      exact hB _ ⟨hs.2.1, hs.2.2.1⟩)
  have hEnd : |integerResidueMass N M a lo hi G φ-
      Real.exp (-G)*(∑ n ∈ openSupport M a lo hi, φ (Real.log n-G))| ≤ Real.exp (-G)*B := by
    unfold integerResidueMass
    rw [← Finset.mul_sum, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos (-G))]
    exact mul_le_mul_of_nonneg_left he (Real.exp_pos (-G)).le
  have ho := open_log_residue_error M a φ ψ G lo hi B D hlohi hφ hψ hB hD
  rw [openSupport_sum M a lo hi (fun x => φ (Real.log x-G))] at ho
  unfold integerDensityMass
  calc
    _ ≤ |integerResidueMass N M a lo hi G φ-
        Real.exp (-G)*(∑ n ∈ openSupport M a lo hi, φ (Real.log n-G))| +
      |Real.exp (-G)*(∑ n ∈ openSupport M a lo hi, φ (Real.log n-G))-
        (∫ t in lo..hi, Real.exp (t-G)*φ (t-G))/(M : ℝ)| := abs_sub_le _ _ _
    _ ≤ Real.exp (-G)*B+Real.exp (-G)*(4*B+2*D*(hi-lo)) := add_le_add hEnd ho
    _ = _ := by ring

theorem integerResidueMass_error_short (N M : ℕ) [NeZero M] (a : ZMod M)
    (φ ψ : ℝ → ℝ) (G lo hi B D : ℝ) (hlohi : lo ≤ hi) (hlen : hi-lo ≤ 1)
    (hN : ⌊Real.exp hi⌋₊ ≤ N)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Continuous ψ)
    (hB : ∀ t ∈ Icc lo hi, |φ (t-G)| ≤ B)
    (hD : ∀ t ∈ Icc lo hi, |ψ (t-G)| ≤ D) :
    |integerResidueMass N M a lo hi G φ-integerDensityMass M lo hi G φ| ≤
      Real.exp (-G)*(5*B+2*D) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD lo ⟨le_rfl, hlohi⟩)
  apply (integerResidueMass_error N M a φ ψ G lo hi B D hlohi hN hφ hψ hB hD).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-G)).le
  nlinarith [mul_le_mul_of_nonneg_left hlen (show 0 ≤ 2*D by positivity)]

theorem log_density_mass_abs_le (φ : ℝ → ℝ) (G lo hi B : ℝ)
    (hlohi : lo ≤ hi) (hlo : G-1 ≤ lo) (hhi : hi ≤ G+1)
    (hφ : Continuous φ) (hB : ∀ t ∈ Icc lo hi, |φ (t-G)| ≤ B) :
    |∫ t in lo..hi, Real.exp (t-G)*φ (t-G)| ≤ 2*Real.exp 1*B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB lo ⟨le_rfl, hlohi⟩)
  have hc : Continuous (fun t => Real.exp (t-G)*φ (t-G)) := by fun_prop
  calc
    _ ≤ ∫ t in lo..hi, |Real.exp (t-G)*φ (t-G)| :=
      intervalIntegral.abs_integral_le_integral_abs hlohi
    _ ≤ ∫ _t in lo..hi, Real.exp 1*B := by
      apply intervalIntegral.integral_mono_on hlohi (hc.abs.intervalIntegrable lo hi) intervalIntegrable_const
      intro t ht
      rw [abs_mul, abs_of_pos (Real.exp_pos (t-G))]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.2])) (hB t ht)
        (abs_nonneg _) (Real.exp_pos 1).le
    _ = (hi-lo)*(Real.exp 1*B) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2*(Real.exp 1*B) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end Ostmann.Arithmetic.IntegerCell
end

end OAI
