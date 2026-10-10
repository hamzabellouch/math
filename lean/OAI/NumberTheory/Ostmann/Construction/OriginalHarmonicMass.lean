import OAI.NumberTheory.Ostmann.Construction.HarmonicBoxMass
import OAI.NumberTheory.Ostmann.Construction.RetainedPrimeNormalization

namespace OAI

/-! # Real box mass with the deleted-prime normalizer -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem PublishedProgressionInput.primeCellSupport_harmonic_error
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) :
    |(∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹) -
      ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹| ≤
        ∑ c, bulkPrimeErrorFactor P Q (u c) := by
  have hs : (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹) =
      ∑ c, ∑ p ∈ primeLogCellSet 1 0 (u c) (v c), (p : ℝ)⁻¹ := by
    unfold primeCellSupport
    rw [Finset.sum_biUnion]
    intro c _ d _ hcd
    exact primeLogCellSet_disjoint 1 0 0 (u c) (v c) (u d) (v d) (Or.inr (hsep c d hcd))
  rw [hs, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  have he := primeLogCell_page_mass_error P hQ (by norm_num : 1 ≤ (1 : ℕ))
    (by omega : 1 ≤ Q) (by simp : Nat.Coprime 0 1) (u c) (v c) (hu c) (huv c) (hshort c)
  rw [primeLogCellMeasure_mass,
    primeGiantMeasure_one_mass P Q 0 (u c) (v c) (by linarith [hu c])] at he
  exact he

/-- Deleting a small amount of original prime mass does not invalidate
the required bound on the normalized real box mass. -/
theorem deleted_harmonic_mass_le_two (S D : Finset ℕ) (a I err : ℝ)
    (ha : 0 < a) (hmass : a ≤ ∑ p ∈ S, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ a / 4)
    (herror : |(∑ p ∈ S, (p : ℝ)⁻¹) - I| ≤ err) (herr : err ≤ a / 4) :
    0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ * I ≤ 2 := by
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  have hp : 0 < ∑ p ∈ S \ D, (p : ℝ)⁻¹ := by linarith
  refine ⟨hp, ?_⟩
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hp).mpr
  have he := (abs_le.mp herror).1
  linarith

theorem PublishedProgressionInput.original_harmonic_box_mass
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c)
    (D : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hmass : a ≤ ∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v ∩ D, (p : ℝ)⁻¹) ≤ a / 4)
    (herror : (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ a / 4) :
    (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v \ D, (p : ℝ)⁻¹)⁻¹ *
      (∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹) ≤ 2 :=
  (deleted_harmonic_mass_le_two _ D a _ _ ha hmass hdeleted
    (P.primeCellSupport_harmonic_error Q hQ u v hu huv hshort hsep) herror).2

end Ostmann

end OAI
