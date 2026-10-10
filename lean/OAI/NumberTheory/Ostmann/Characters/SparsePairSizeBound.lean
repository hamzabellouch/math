import OAI.NumberTheory.Ostmann.Characters.SparsePairEnergyBudget
import OAI.NumberTheory.Ostmann.Supply.ConstantModeBudget
import OAI.NumberTheory.Ostmann.Characters.SparseCoverageContradiction

namespace OAI

/-! # Removing the normalizations in the sparse pair bound -/
namespace Ostmann
open scoped Classical BigOperators

theorem normalized_pair_energy_bound (s w α r D a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hw : w = a⁻¹ * b⁻¹ * s)
    (henergy : α ^ 2 * w ^ 2 ≤ r ^ 2 * (D / a) * (D / b)) :
    α ^ 2 * s ^ 2 ≤ r ^ 2 * D ^ 2 * (a * b) := by
  have hh := mul_le_mul_of_nonneg_right henergy (sq_nonneg (a * b))
  rw [hw] at hh
  convert hh using 1 <;> field_simp

theorem sparse_pair_coverage_size_bound {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K)
    {ι κ : Type*} (A : Finset ι) (B : Finset κ) (hA : A.Nonempty) (hB : B.Nonempty)
    (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i)
    (α D c X T : ℝ) (hα : 0 ≤ α) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hT : 0 ≤ T)
    (hEA : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 ≤ D / A.card)
    (hEB : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates B (fun y => tensorPointCoordinates p
        (fun i => Finset.univ \ S i) (b y)))) ^ 2 ≤ D / B.card)
    (hcover : c * (∏ i, sparseKernelUnitFactor (p i)
        (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)) * X ≤
      T * ∑ x ∈ A, ∑ y ∈ B, sparseSubsetWeight p S K (fun i => a x i - b y i)) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    c * U * X * α ^ 2 ≤
      T * (2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) * D ^ 2 := by
  intro U
  have hmA : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hmB : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  obtain ⟨hU, _, he⟩ := sparse_pair_average_energy_budget p S hS hSp hp hlo hhi
    ε hε hεsmall hL1 L hL hH K hK A B a b ha hb α (D / A.card) (D / B.card)
      hα (div_nonneg hD hmA.le) hEA hEB
  have hAsize := constant_mode_card_bound α D A.card _ hα hmA
    (lowMode_tensor_energy_one_le p S A hA a (2 * K)) hEA
  have hBsize := constant_mode_card_bound α D B.card _ hα hmB
    (lowMode_tensor_energy_one_le p (fun i => Finset.univ \ S i) B hB b (2 * K)) hEB
  have hsize : α ^ 2 * ((A.card : ℝ) * B.card) ≤ D ^ 2 := by
    have hh := mul_le_mul hAsize hBsize (mul_nonneg hα hmB.le) hD
    nlinarith only [hh]
  apply coverage_energy_size_bound _ c U X α T _ D ((A.card : ℝ) * B.card)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sparseSubsetWeight_nonneg p S K _)
    hc hU.le hX hα hT (by positivity) hD hcover _ hsize
  exact normalized_pair_energy_bound _ _ _ _ _ _ _ hmA hmB rfl he

end Ostmann

end OAI
