import OAI.Probability.InvariantIsing.Magnetic.MagneticLevelModulus
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPath

namespace OAI

/-! Height continuity after block averaging, uniformly in block size
and in every optimizing root bias. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal
namespace InvariantIsing

lemma magneticBlockLevel_abs_sub_le {N : ℕ} (hN : 0 < N) (h : FieldStep)
    {V : ℝ} (hV : h.height (Fin.last h.depth) ≤ V) (m : Fin N → ℝ)
    (i j : Fin (h.depth+1)) :
    |magneticBlockLevel h m i-magneticBlockLevel h m j| ≤
      |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  unfold magneticBlockLevel
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ k, |magneticFieldLevel h (m k) i-magneticFieldLevel h (m k) j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ _k : Fin N,
        |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => magneticFieldLevel_abs_sub_le h hV (m k) i j) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

lemma magneticBlockPath_on_cell {N : ℕ} (hN : 0 < N) (h : FieldStep) (m : Fin N → ℝ)
    (i : Fin (h.depth+1)) {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    magneticBlockPath hN h m s = magneticBlockLevel h m i :=
  fieldLevelPath_on_cell h _ _ _ i hs

end InvariantIsing

end

end OAI
