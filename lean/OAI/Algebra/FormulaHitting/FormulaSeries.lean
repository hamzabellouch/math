import OAI.Algebra.FormulaHitting.Evaluation
import OAI.Algebra.FormulaHitting.Series

namespace OAI

noncomputable section
namespace NCHitting
namespace Formula

variable {F : Type*} {n : ℕ} [Field F]

def series (f : Formula F n) : PowerSeries F :=
  f.polynomial.sum (fun w a => PowerSeries.C a * wordSeries w)

theorem series_eq_smul_sum (f : Formula F n) :
    f.series = f.polynomial.sum (fun w a => a • wordSeries w) := by
  simp only [series, PowerSeries.smul_eq_C_mul]

theorem series_eq_sum_of_cutoff (f : Formula F n) (d : ℕ)
    (hcut : ∀ w, d ≤ w.length → f.coeff w = 0) :
    f.series = ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k,
      PowerSeries.C (f.coeff w) * wordSeries w := by
  exact sum_eq_sum_wordsOfLength f.polynomial hcut _ (by intro w; simp)

theorem series_eq_sum_wordsOfLength (f : Formula F n) {s : ℕ} (hs : f.size ≤ s) :
    f.series = ∑ k ∈ Finset.range (s + 1), ∑ w ∈ wordsOfLength n k,
      PowerSeries.C (f.coeff w) * wordSeries w := by
  apply f.series_eq_sum_of_cutoff
  intro w hw
  exact f.coeff_eq_zero_of_length_gt w (by omega)

end Formula
end NCHitting

end

end OAI
