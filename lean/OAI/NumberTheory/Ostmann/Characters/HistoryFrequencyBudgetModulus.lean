import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsModulus

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryFrequencyLabels

theorem labels_length (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) :
    (labels k p s t).length = 2^(k+1)-1 := by
  induction k generalizing p s with
  | zero => simp [labels]
  | succ k ih =>
    simp only [labels,List.length_cons,List.length_append,ih]
    have hp : 0 < 2^(k+1) := by positivity
    rw [show k+1+1=(k+1)+1 by omega,pow_succ]
    omega

theorem modulus_le_pow {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} (V : ℕ)
    (hV : ∀ q z, (q,z) ∈ labels k p s t → z.natAbs ≤ V) :
    modulus k p s t ≤ V^(2^(k+1)-1) := by
  have h := List.prod_le_pow_length
    ((labels k p s t).map (fun a => a.2.natAbs)) V (by
      intro z hz
      obtain ⟨⟨q,w⟩,hw,rfl⟩ := List.mem_map.mp hz
      exact hV q w hw)
  simpa only [List.length_map,labels_length,modulus] using h

theorem modulus_le_exp {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} (T : ℝ)
    (hT : ∀ q z, (q,z) ∈ labels k p s t → (z.natAbs:ℝ) ≤ Real.exp T) :
    (modulus k p s t:ℝ) ≤ Real.exp ((2^(k+1)-1:ℕ)*T) := by
  have hnat : modulus k p s t ≤ ⌊Real.exp T⌋₊^(2^(k+1)-1) :=
    modulus_le_pow _ (fun q z hz => (Nat.le_floor_iff (Real.exp_pos _).le).mpr (hT q z hz))
  have hcast : (modulus k p s t:ℝ) ≤ (⌊Real.exp T⌋₊:ℝ)^(2^(k+1)-1) := by
    exact_mod_cast hnat
  calc
    _ ≤ (Real.exp T)^(2^(k+1)-1) := hcast.trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.exp_pos _).le) _)
    _ = _ := (Real.exp_nat_mul _ _).symm

end Ostmann.Characters.HistoryFrequencyLabels

namespace Ostmann.Characters.HistoryFrequencyBudget
open HistoryFrequencyLabels

theorem supported_modulus_le_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    {j : ℕ} {s : ℤ} {t : HistoryReconstruction.Tree j}
    (h : RangeSupported (ranges a m j) j [] s t) :
    (modulus j [] s t:ℝ) ≤
      Real.exp (((2^(j+1)-1:ℕ):ℝ)*linearEnvelope a j*m) := by
  have hb := modulus_le_exp (linearEnvelope a j*m) (fun q z hz => by
    have hs := (mem_signedRange _ _).mp (mem_labels_range (ranges a m j) h hz)
    have hc : (z.natAbs:ℝ) ≤ (bound a m (j-q.length):ℝ) := by exact_mod_cast hs.2
    exact hc.trans ((bound_le_exp _ _ _).trans
      (Real.exp_le_exp.mpr (exponent_le_linear ha hm (Nat.sub_le _ _)))))
  simpa only [mul_assoc] using hb

theorem supported_precision_le_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    {j : ℕ} {s : ℤ} {t : HistoryReconstruction.Tree j}
    (h : RangeSupported (ranges a m j) j [] s t) (K : ℕ) :
    ((modulus j [] s t)^(K+2):ℕ) ≤
      Real.exp (((K+2:ℕ):ℝ)*((2^(j+1)-1:ℕ):ℝ)*linearEnvelope a j*m) := by
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) (supported_modulus_le_exp ha hm h) (K+2)
  rw [← Real.exp_nat_mul] at hh
  simpa only [Nat.cast_pow,mul_assoc] using hh

end Ostmann.Characters.HistoryFrequencyBudget

end

end OAI
