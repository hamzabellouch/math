import OAI.NumberTheory.TotientAsymptotic.WitnessAggregation
import OAI.NumberTheory.TotientAsymptotic.WitnessGrid
import OAI.NumberTheory.TotientAsymptotic.CubeBoundary
import OAI.NumberTheory.TotientAsymptotic.TailCofactor
import OAI.NumberTheory.TotientAsymptotic.CofactorGrowth

namespace OAI

/-! The reciprocal totient weights can be aggregated at fixed cofactor,
including tails containing repeated prime factors. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

/-- One full-dimensional volume controls a fixed-cofactor witness family.
The only arithmetic input is the published prime-box estimate. -/
theorem cofactor_witness_aggregation (hbox : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H R a : ℕ} {s : ℝ}, 0 ≤ s → P H ≤ H →
      ∀ (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
        (T : Set (Fin (R+(H-P H)) → ℝ)),
      (∀ η ∈ W, IsWitness H s η) → (∀ η ∈ W, η.cofactor=a) →
      (∀ η ∈ W, MeasurableSet (S η)) → volume T ≠ ⊤ →
      (∀ η ∈ W, ∀ u ∈ S η, ∀ v : Fin (H-P H) → ℝ,
        (∀ i, |tailVector η i-v i| ≤ 1) → joinCoordinates R (H-P H) (u,v) ∈ T) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η)) ≤
        (a.totient : ℝ)⁻¹*C*volume.real T := by
  obtain ⟨C, hC, hgrid⟩ := witnessGrid_prime_mass_bound hbox
  refine ⟨C, hC, ?_⟩
  intro H R a s hs hPH W S T hW hcof hS hT henclose
  have hweight (η) (hη : η ∈ W) :
      ((w η).totient : ℝ)⁻¹ ≤ (a.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η) := by
    simpa only [hcof η hη] using tail_reciprocal_vector (hW η hη) hPH
  have hsum := witness_tail_box_aggregation W S (witnessGrid W) T C hC.le hW hcof hS hT
    (fun η hη => tailPrimeVector_mem_grid W hW hη) (hgrid hs hPH W hW)
    (by
      intro η hη b _ hb u hu v hv
      exact henclose η hη u hu v (unitGridCell_coordinate_distance hb hv))
  calc
    _ ≤ ∑ η ∈ W, ((a.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η))*volume.real (S η) :=
      Finset.sum_le_sum (fun η hη => mul_le_mul_of_nonneg_right (hweight η hη) measureReal_nonneg)
    _ = (a.totient : ℝ)⁻¹*∑ η ∈ W,
        reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring
    _ ≤ (a.totient : ℝ)⁻¹*(C*volume.real T) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Summing all allowed cofactors retains only the subpolynomial envelope,
not the number of witnesses. -/
theorem all_cofactor_witness_aggregation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H R : ℕ} {s : ℝ}, s ∈ Set.Ico (0 : ℝ) 1 → P H ≤ H →
      ∀ (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
        (T : Set (Fin (R+(H-P H)) → ℝ)),
      (∀ η ∈ W, IsWitness H s η) → (∀ η ∈ W, MeasurableSet (S η)) → volume T ≠ ⊤ →
      (∀ η ∈ W, ∀ u ∈ S η, ∀ v : Fin (H-P H) → ℝ,
        (∀ i, |tailVector η i-v i| ≤ 1) → joinCoordinates R (H-P H) (u,v) ∈ T) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η)) ≤
        C*Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T := by
  obtain ⟨C, hC, hfixed⟩ := cofactor_witness_aggregation hbox
  obtain ⟨D, hD, hcof⟩ := tail_cofactor_sum hmertens
  refine ⟨C*D, mul_pos hC hD, ?_⟩
  intro H R s hs hPH W S T hW hS hT henclose
  have hmaps : ∀ η ∈ W, η.cofactor ∈ Finset.Icc 1 (tailCofactorBound H) := by
    intro η hη
    exact Finset.mem_Icc.mpr (witness_cofactor_bound hs (hW η hη))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H),
        (a.totient : ℝ)⁻¹*C*volume.real T := by
      apply Finset.sum_le_sum
      intro a _
      apply hfixed hs.1 hPH (W.filter (fun η => η.cofactor=a)) S T
      · intro η hη
        exact hW η (Finset.mem_filter.mp hη).1
      · intro η hη
        exact (Finset.mem_filter.mp hη).2
      · intro η hη
        exact hS η (Finset.mem_filter.mp hη).1
      · exact hT
      · intro η hη
        exact henclose η (Finset.mem_filter.mp hη).1
    _ = (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*C*volume.real T := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ (D*Real.exp ((4*(lam/rho))*cofactorScale H))*C*volume.real T := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      apply mul_le_mul_of_nonneg_right _ hC.le
      have he : 4*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ =
          (4*(lam/rho))*cofactorScale H := by unfold cofactorScale; ring
      simpa only [he] using hcof H
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
