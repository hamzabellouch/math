import OAI.NumberTheory.Ostmann.Construction.HarmonicBoxMass

namespace OAI

/-! # Restoring exceptional prime atoms with the original normalization -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeSubsetLogMeasure_restored_mass (S D : Finset ℕ)
    (hS : (∑ p ∈ S \ D, (p : ℝ)⁻¹) ≠ 0) :
    (primeSubsetLogMeasure S (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹).real Set.univ =
      1 + (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ * ∑ p ∈ S ∩ D, (p : ℝ)⁻¹ := by
  rw [primeSubsetLogMeasure_mass S _ (by positivity)]
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  rw [← hs, mul_add, inv_mul_cancel₀ hS, add_comm]

/-- The modulus-one comparison gives the exact error in replacing all
harmonic prime atoms by the real harmonic masses of the cells. -/
theorem PublishedProgressionInput.harmonic_cells_mass_error
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (Z : ℝ) (hZ : 0 ≤ Z) :
    |(bulkCellMixture Z (fun c => primeLogCellMeasure 1 0 (u c) (v c))).real Set.univ -
      Z * ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹| ≤
      Z * ∑ c, bulkPrimeErrorFactor P Q (u c) := by
  let μ := fun c => primeLogCellMeasure 1 0 (u c) (v c)
  let ν := fun c => primeGiantMeasure P Q 1 0 (u c) (v c)
  let _ : ∀ c, IsFiniteMeasure (ν c) := fun c =>
    finite_primeGiantMeasure P Q 1 0 (u c) (v c) (lt_of_lt_of_le zero_lt_one (hu c))
  have h := (bulkConstant (σ := Unit) 1).cellMixture_comparison Z hZ μ ν ()
    (fun c => bulkPrimeErrorFactor P Q (u c)) (fun c _ => by
      rw [bulkConstant_average_one, bulkConstant_average_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      exact primeLogCell_page_mass_error P hQ (by norm_num) (by omega) (by simp)
        (u c) (v c) (hu c) (huv c) (hshort c)) (fun _ => 0)
  rw [bulkConstant_average_one, bulkConstant_average_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  rw [bulkCellMixture_mass Z hZ ν] at h
  simpa only [ν, primeGiantMeasure_one_mass P Q 0 _ _ (lt_of_lt_of_le zero_lt_one (hu _))] using h

/-- Small exceptional deletions and the interval error share the same unit
error budget, while the normalization remains that of the deleted prime set. -/
theorem PublishedProgressionInput.restored_harmonic_cells_le_two
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c)
    (D : Finset ℕ)
    (hS : (∑ p ∈ primeCellSupport 1 (fun _ => 0) u v \ D, (p : ℝ)⁻¹) ≠ 0)
    (herror :
      (∑ p ∈ primeCellSupport 1 (fun _ => 0) u v \ D, (p : ℝ)⁻¹)⁻¹ *
        ((∑ p ∈ primeCellSupport 1 (fun _ => 0) u v ∩ D, (p : ℝ)⁻¹) +
          ∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ 1) :
    (∑ p ∈ primeCellSupport 1 (fun _ => 0) u v \ D, (p : ℝ)⁻¹)⁻¹ *
      ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹ ≤ 2 := by
  let S := primeCellSupport 1 (fun _ : C => 0) u v
  let Z := (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹
  have hz : 0 ≤ Z := by positivity
  have he := P.harmonic_cells_mass_error Q hQ u v hu huv hshort Z hz
  have hm := primeSubsetLogMeasure_restored_mass S D hS
  have hsep' : ∀ c d, c ≠ d → ¬Nat.ModEq 1 (0 : ℕ) 0 ∨ v c ≤ u d ∨ v d ≤ u c :=
    fun c d hcd => Or.inr (hsep c d hcd)
  change (primeSubsetLogMeasure (primeCellSupport 1 (fun _ : C => 0) u v) Z).real Set.univ =
    1 + Z * ∑ p ∈ S ∩ D, (p : ℝ)⁻¹ at hm
  rw [primeSubsetLogMeasure_cells 1 (fun _ : C => 0) u v Z hsep'] at hm
  rw [hm] at he
  have hlow := (abs_le.mp he).1
  change Z * ((∑ p ∈ S ∩ D, (p : ℝ)⁻¹) + ∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ 1 at herror
  change Z * ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹ ≤ 2
  rw [mul_add] at herror
  linarith

end Ostmann

end OAI
