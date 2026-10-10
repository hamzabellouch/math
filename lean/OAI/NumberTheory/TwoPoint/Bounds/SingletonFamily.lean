import OAI.NumberTheory.TwoPoint.Bounds.OrderedPrimeSystems
import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting

namespace OAI

/-! Sum the reciprocal savings of fixed singleton relation records. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

/-- The nonzero tests stay in every system event, so the estimate remains
valid for all resampled prime assignments. -/
theorem singleton_family_bound (system : I → OrderedPrimeSystem ι) (K : ℕ)
    (hsize : ∀ i, K ≤ (system i).size)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log N) / H ≤ 1)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    (∑ i, weight i * ∑ x : ι → P,
      if (system i).Holds (integerPrimeAssignment Subtype.val x)
        then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      (∑ i, weight i) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ K := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hd : 0 ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / H := by positivity
  rw [mul_assoc, sum_mul]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply ((system i).reciprocal_sum_bound P hP hV H N hH hN hlo hhi).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hd hdelta (hsize i))
    (pow_nonneg (by linarith) _)

/-- Outside numerical data is averaged separately from the finite
combinatorial record, preserving the unrestricted reciprocal mass. -/
theorem outer_singleton_family_bound
    (Ξ : I → Type*) [∀ i, Fintype (Ξ i)]
    (system : ∀ i, Ξ i → OrderedPrimeSystem ι) (K : ℕ)
    (hsize : ∀ i x, K ≤ (system i x).size)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log N) / H ≤ 1)
    (outerWeight : ∀ i, Ξ i → ℝ) (hout : ∀ i x, 0 ≤ outerWeight i x)
    (outerMass : ℝ) (hmass : ∀ i, ∑ x, outerWeight i x ≤ outerMass)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    (∑ i, weight i * ∑ x, outerWeight i x * ∑ y : ι → P,
      if (system i x).Holds (integerPrimeAssignment Subtype.val y)
        then ∏ z, ((y z).val : ℝ)⁻¹ else 0) ≤
      (∑ i, weight i) * outerMass * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ K := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hd : 0 ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / H := by positivity
  have hs (i : I) := singleton_family_bound (system i) K (hsize i) P hP hV H N hH hN
    hlo hhi hdelta (outerWeight i) (hout i)
  rw [mul_assoc, mul_assoc, sum_mul]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply (hs i).trans
  have hm := mul_le_mul_of_nonneg_right (hmass i)
    (mul_nonneg (pow_nonneg (show 0 ≤ primeHarmonicMass P by linarith) (Fintype.card ι)) (pow_nonneg hd K))
  simpa only [mul_assoc] using hm

/-- The exact finite code count bounds the total nonnegative record weight. -/
theorem singleton_record_weight_bound (R N D : ℕ)
    (encode : I → CrudeWordCode R N D) (hinj : Function.Injective encode)
    (weight : I → ℝ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, weight i ≤ W) :
    (∑ i, weight i) ≤ (Fintype.card (CrudeWordCode R N D) : ℝ) * W := by
  have hcard := Fintype.card_le_of_injective encode hinj
  calc
    _ ≤ ∑ _i : I, W := sum_le_sum (fun i _ => hw i)
    _ = (Fintype.card I : ℝ) * W := by simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hW

end TwoPointCorrelations

end OAI
