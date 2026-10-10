import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseInputWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseBitWork

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

theorem physicalSource_mem {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) (a : α) (ha : a ∈ physicalSource source node) : a ∈ source := by
  exact List.mem_of_mem_take (List.mem_of_mem_drop ha)

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)

noncomputable def symbolicComputedExecutionCoarseBitWork
    (execution : PhysicalCoarseExecution (R := R) source target N
      (integerParameters N).P (inputHeight N) B depth) : ℝ :=
  physicalFamilyCoarseBitWork source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    execution.2.2 depth (16384 * inputHeight N + 5) encode
    (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length)) execution.1

theorem symbolicComputedExecutionCoarseBitWork_integrable :
    Integrable (symbolicComputedExecutionCoarseBitWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedExecutionCoarseBitWork source target N depth encode
      (outcome.1, (fun _ => 0, outcome.2))
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
theorem symbolicComputedExecutionCoarseBitWork_bound
    (hcost : ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (_hB : NeZero B) (draw : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseEntryBinaryCost N B d x y draw : ℝ) ≤ (inputHeight N : ℝ) ^ 36 *
        ((coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draw : ℝ) +
          (x.length + 1 : ℕ)))
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hsize : source.length + target.length ≤ N)
    (hsymbols : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3)
    (execution : PhysicalCoarseExecution (R := R) source target N
      (integerParameters N).P (inputHeight N) B depth) :
    symbolicComputedExecutionCoarseBitWork source target N depth encode execution ≤
      (inputHeight N : ℝ) ^ 36 *
      (symbolicComputedExecutionCoarseWork source target N depth encode execution +
       physicalFamilyCoarseInputWork source target N (integerParameters N).P (inputHeight N)
        (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
        (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
        (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
        (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
        (clampedSeedNat (physicalCoarseSeedTable source target N B depth execution.1)) execution.2.2
        (16384 * inputHeight N + 5) encode
        (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
          (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) := by
  apply physicalFamilyCoarseBitWork_bound
  intro entry
  have hx := physicalSource_length_le source entry.1
  have hy : (substring target entry.2.lo entry.2.hi).length ≤ target.length := by
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  have hxy : coarseEntryWidth (physicalSource source entry.1)
      (substring target entry.2.lo entry.2.hi) ≤ N := max_le (by omega) (by omega)
  have hsy : ∀ a ∈ physicalSource source entry.1 ++ substring target entry.2.lo entry.2.hi,
      Nat.size a ≤ inputHeight N ^ 3 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hsymbols a (List.mem_append_left _ (physicalSource_mem source entry.1 a ha))
    · exact hsymbols a (List.mem_append_right _
        (List.mem_of_mem_take (List.mem_of_mem_drop ha)))
  exact hcost B (depth entry) _ _ hB (hdepth entry) hxy hsy inferInstance (execution.1 entry)
end Symbolic

noncomputable def computedExecutionCoarseBitWork (source target : List ℕ) (N : ℕ) :=
  symbolicComputedExecutionCoarseBitWork (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
    (B := (integerParameters N).B) source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2))

theorem computedExecutionCoarseBitWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ execution : ComputedExecutionOutcome source target N,
        computedExecutionCoarseBitWork source target N execution ≤
          (inputHeight N : ℝ) ^ 36 * (computedExecutionCoarseWork source target N execution +
            computedExecutionCoarseInputWork source target N execution) := by
  filter_upwards [coarseEntryBinaryCost_computed_bound] with N hN
  intro source target hsize hsymbols execution
  exact symbolicComputedExecutionCoarseBitWork_bound source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    hN rfl (fun _ => rfl) hsize hsymbols execution

theorem computedExecutionCoarseBitWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseBitWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseBitWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

theorem computedExecutionCoarseBitWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      (∫ execution, computedExecutionCoarseBitWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have he : 0 < epsilon / 3 := by positivity
  filter_upwards [computedExecutionCoarseBitWork_bound,
    computedExecutionCoarseWork_expected_near_linear (epsilon / 3) he,
    computedExecutionCoarseInputWork_expected_near_linear (epsilon / 3) he,
    fixed_height_power_subpolynomial 36 (epsilon / 3) he,
    constant_le_rpow_eventually 2 (epsilon / 3) he] with N hb hc hi hp ht
  intro source target hsize hsymbols
  let μ := computedExecutionLaw source target N
  have hic := computedExecutionCoarseWork_integrable source target N
  have hii := computedExecutionCoarseInputWork_integrable source target N
  have hbound : (∫ execution, computedExecutionCoarseBitWork source target N execution ∂μ) ≤
      (inputHeight N : ℝ) ^ 36 * ((∫ execution, computedExecutionCoarseWork source target N execution ∂μ) +
        ∫ execution, computedExecutionCoarseInputWork source target N execution ∂μ) := by
    calc
      _ ≤ ∫ execution, (inputHeight N : ℝ) ^ 36 *
          (computedExecutionCoarseWork source target N execution +
            computedExecutionCoarseInputWork source target N execution) ∂μ :=
        integral_mono (computedExecutionCoarseBitWork_integrable source target N)
          ((hic.add hii).const_mul _) (hb source target hsize hsymbols)
      _ = _ := by rw [integral_const_mul, integral_add hic hii]
  have hsum := add_le_add (hc source target hsize) (hi source target hsize)
  calc
    _ ≤ (inputHeight N : ℝ) ^ 36 * (2 * (N + 2 : ℝ) ^ (1 + epsilon / 3)) :=
      hbound.trans (mul_le_mul_of_nonneg_left (by linarith only [hsum]) (by positivity))
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 3) * (2 * (N + 2 : ℝ) ^ (1 + epsilon / 3)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 3) *
        ((N + 2 : ℝ) ^ (epsilon / 3) * (N + 2 : ℝ) ^ (1 + epsilon / 3)) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
      congr 1
      ring

end EditApproximation

end OAI
