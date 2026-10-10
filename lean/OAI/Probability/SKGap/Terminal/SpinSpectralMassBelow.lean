import Mathlib
import OAI.Probability.SKGap.Localization.LinearObservable

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff
open MeasureTheory

noncomputable def spinSpectralMassBelow {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (L : ℝ) : ℝ :=
  ∑ a, if spinEigenvalues J hJ hdiag a ≤ L then spinSpectralMass J hJ hdiag a else 0

lemma spinSpectralMassBelow_nonneg {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (L : ℝ) :
    0 ≤ spinSpectralMassBelow J hJ hdiag L := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact spinSpectralMass_nonneg J hJ hdiag a
  · rfl

lemma spinSpectralMeasure_Iic {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (L : ℝ) :
    spinSpectralMeasure J hJ hdiag (Set.Iic L) =
      ENNReal.ofReal (spinSpectralMassBelow J hJ hdiag L) := by
  simp only [spinSpectralMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    spinSpectralMassBelow]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs with h
    · simp only [Measure.dirac_apply' _ measurableSet_Iic, Set.mem_Iic, h,
        Set.indicator_of_mem, smul_eq_mul, Pi.one_apply, mul_one]
    · simp [h]
  · intro a _
    split_ifs
    · exact spinSpectralMass_nonneg J hJ hdiag a
    · rfl

lemma spinCorrelation_eq_spectralSum {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (t : ℝ) :
    spinCorrelation J t = ∑ a, spinSpectralMass J hJ hdiag a *
      Real.exp (-spinEigenvalues J hJ hdiag a * t) := by
  rw [← spinSpectralMeasure_integral J hJ hdiag (fun u => Real.exp (-u*t)),
    spinSpectralMeasure_correlation]
  rfl

lemma spinCorrelation_lower_of_mass {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (L t : ℝ) (ht : 0 ≤ t) :
    spinSpectralMassBelow J hJ hdiag L * Real.exp (-L * t) ≤ spinCorrelation J t := by
  rw [spinCorrelation_eq_spectralSum J hJ hdiag, spinSpectralMassBelow, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h
  · apply mul_le_mul_of_nonneg_left _ (spinSpectralMass_nonneg J hJ hdiag a)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h) ht)
  · simp only [zero_mul]
    exact mul_nonneg (spinSpectralMass_nonneg J hJ hdiag a) (Real.exp_pos _).le

theorem worstContinuous_lower_from_spectralMass {n : ℕ} (hn : 0 < n)
    (J : Interaction n) (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {γ V c L t : ℝ} (ht : 0 ≤ t) (hγ : 0 < γ) (hgap : HasGap J γ)
    (hV : 1 ≤ γ * V) (hc : 0 < c) (hmass : c ≤ spinSpectralMassBelow J hJ hdiag L)
    (hvar : ∀ x, semigroup J t (fun y => overlap x y ^ 2) x -
      (semigroup J t (overlap x) x) ^ 2 ≤ (n : ℝ) * V) :
    (n : ℝ) * c ^ 2 * Real.exp (-2 * L * t) * (1 - worstContinuous J t) ≤ 8 * V := by
  have he : c * Real.exp (-L * t) ≤ spinCorrelation J t :=
    (mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le).trans
      (spinCorrelation_lower_of_mass J hJ hdiag L t ht)
  have hl := worstContinuous_lower_from_spin hn J ht hγ hgap hV
    (mul_pos hc (Real.exp_pos _)) he hvar
  have hexp : Real.exp (-L * t) ^ 2 = Real.exp (-2 * L * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [mul_pow, hexp] at hl
  simpa only [mul_assoc] using hl

end SKGapCutoff

end

end OAI
