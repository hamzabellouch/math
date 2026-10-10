import OAI.MeasureTheory.Falconer.Fourier.FourierBandDecomposition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_fourier_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t N : ℕ} (hat : a ≤ t) (htN : t ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hbase : (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2) ≤ B)
    (hshell : ∀ v ∈ Finset.Ioc a t,
      (2:ℝ)^(-(a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤ B) :
    (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) ≤
      (1+2*(N:ℝ))*B := by
  have hsum := Finset.sum_le_sum hshell
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((Finset.Ioc a t).card:ℝ) ≤ (N:ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast (show t-a ≤ N by omega)
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [fourier_dyadic_band_decomposition μ hat]
  have he : (2:ℝ)^(-(a:ℝ))*(2*∑ v ∈ Finset.Ioc a t,
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) =
      2*∑ v ∈ Finset.Ioc a t, (2:ℝ)^(-(a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) := by
    rw [← Finset.mul_sum]
    ring
  rw [mul_add,he]
  nlinarith

end PlanarFalconer

end OAI
