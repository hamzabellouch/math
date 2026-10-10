import OAI.MeasureTheory.Falconer.Recursion.DescriptorMaskFailure
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Recursion.RetainedPairMasks

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem outerEntry_le (m₁ m₂ : ℝ → ℝ) (N : ℕ) (β : ℝ) : outerEntry m₁ m₂ N β ≤ N := by
  apply Finset.sup_le
  intro n hn
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)

theorem actualClassMeasure_carry (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) :
    actualClassMeasure Q μ N B T Q.carrierᶜ = 0 := by
  rw [actualClassMeasure,normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

noncomputable def outerAllEntryFailure (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (x : Plane) : Set UnitCircle :=
  ⋃ c ∈ Finset.range (N+1), {dir | outerEndpointMask Q ρ m N lam sig kap c x dir ≠ 1}

theorem measurableSet_outerAllEntryFailure (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) :
    MeasurableSet {z : Plane × UnitCircle | z.2 ∈ outerAllEntryFailure Q ρ m N lam sig kap z.1} := by
  have he : {z : Plane × UnitCircle | z.2 ∈ outerAllEntryFailure Q ρ m N lam sig kap z.1} =
      ⋃ c ∈ Finset.range (N+1), {z : Plane × UnitCircle | outerEndpointMask Q ρ m N lam sig kap c z.1 z.2 ≠ 1} := by
    ext z
    simp only [outerAllEntryFailure,mem_ofPred_eq,mem_iUnion]
  rw [he]
  exact Finset.measurableSet_biUnion _ (fun entry _ =>
    (measurableSet_eq_fun (measurable_outerEndpointMask Q ρ m N lam sig kap entry)
      measurable_const).compl)

theorem ae_outerAllEntryFailure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (hcarry : ρ Q.carrierᶜ = 0) (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (ha : SourceAngularBounds Q ρ m N lam sig) :
    ∀ᵐ x ∂ρ, sourceArcLength (outerAllEntryFailure Q ρ m N lam sig kap x) ≤
      ((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hcard (entry : ℕ) :
      ((outerDescriptorList m N (sourcePolicyBlock N kap) entry).card : ENNReal) ≤
        (((N+1)^3+1 : ℕ) : ENNReal) := by
    exact_mod_cast outerDescriptorList_card m hq (c := entry)
  have hx : ∀ᵐ x ∂ρ, ∀ c : ℕ, c ≤ N → sourceArcLength
      {dir | outerEndpointMask Q ρ m N lam sig kap c x dir ≠ 1} ≤
        (((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
    apply ae_all_iff.mpr
    intro c
    by_cases hc : c ≤ N
    · filter_upwards [ae_listMask_failure_bound Q hQ ρ hcarry m N lam sig (sourceSmoothingLevels sig kap) ha
        (outerDescriptorList m N (sourcePolicyBlock N kap) c) (outerDescriptorList_valid m hq hc)] with x hx
      intro _
      exact hx.trans (mul_le_mul_left (hcard c) _)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hc h))
  filter_upwards [hx] with x hx
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _c ∈ Finset.range (N+1), (((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hx c (Nat.le_of_lt_succ (Finset.mem_range.mp hc))
    _ = _ := by simp [mul_assoc]

end PlanarFalconer

end OAI
