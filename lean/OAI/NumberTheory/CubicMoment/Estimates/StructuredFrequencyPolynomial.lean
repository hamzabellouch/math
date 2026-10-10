import OAI.NumberTheory.CubicMoment.Estimates.StructuredCoefficientEnergy

namespace OAI

/-! Exact squarefree frequency polynomial with the numerator, height and
excluded-prime factors retained in its actual coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredFrequencySupport (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter Squarefree

def structuredFrequencyCoefficient (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (z : Eisenstein) : ℂ :=
  if IsCoprime z e then
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*cubicSymbol z v else 0

lemma structuredPrimeSum_eq_frequency (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    structuredPrimeSum h 1 v e u W X Z =
      ∑ z ∈ structuredFrequencySupport W X Z,
        structuredFrequencyCoefficient v e u W X Z z*cubicSymbol z h := by
  unfold structuredPrimeSum structuredFrequencySupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz
  by_cases hsf : Squarefree z
  · rw [ite_eq_left hsf]
    by_cases hc : IsCoprime z e
    · simp only [ite_eq_left hc,structuredFrequencyCoefficient,one_pow,mul_one,
        cubicSymbol_mul_upper hp]
      ring
    · simp only [ite_eq_right hc,structuredFrequencyCoefficient,zero_mul]
  · have he : primeMomentCoefficient W X Z z = 0 := by
      simp only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hsf]
    simp only [he,zero_mul,ite_eq_right hsf,ite_self]

lemma structuredFrequencySupport_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) : ∀ z ∈ structuredFrequencySupport W X Z,
      primary z ∧ Squarefree z ∧ norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  intro z hz
  obtain ⟨hz,hsf⟩ := Finset.mem_filter.mp hz
  exact ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
    hsf,(coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩

lemma structuredFrequencyCoefficient_energy_le (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredFrequencyCoefficient v e u W X Z z‖^2) ≤
    ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2 := by
  have hsub : structuredFrequencySupport W X Z ⊆
      orderedConvolutionSupport (coordinatePrimeSupport W X Z) := Finset.filter_subset _ _
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => sq_nonneg ‖primeMomentCoefficient W X Z z‖))
  apply Finset.sum_le_sum
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) (Finset.mem_filter.mp hz).1
  apply pow_le_pow_left₀ (_root_.norm_nonneg _)
  unfold structuredFrequencyCoefficient
  split_ifs
  · rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp v)
  · simp

end CubicFirstMoment

end

end OAI
