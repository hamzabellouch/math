import OAI.NumberTheory.DukePrimeDegree.Dynamics.TranslationInvariantProduct

namespace OAI

/-!
# Splitting off a right-invariant, possibly noncommutative, neutral factor

Inversion reduces uniqueness of right Haar slices to the existing left
Haar uniqueness theorem. No unimodularity assumption or conclusion is
used: the neutral factor is explicitly a right Haar measure.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace DukePrimeDegree

variable {Z H : Type*} [MeasurableSpace Z] [MeasurableSpace H]
  [TopologicalSpace Z] [TopologicalSpace H] [BorelSpace Z] [BorelSpace H]
  [T2Space Z] [T2Space H] [Group H] [IsTopologicalGroup H]

omit [TopologicalSpace Z] [BorelSpace Z] [T2Space Z] [T2Space H] in
theorem secondCoordinateSlice_rightInvariant
    (ρ : Measure (Z × H)) (A : Set Z) (hA : MeasurableSet A)
    (hinv : ∀ h : H, ρ.map (fun z => (z.1, z.2 * h)) = ρ) :
    Measure.IsMulRightInvariant (secondCoordinateSlice ρ A) := by
  constructor
  intro h
  ext B hB
  have hm : Measurable (fun x : H => x * h) := (continuous_mul_const h).measurable
  have hM : Measurable (fun z : Z × H => (z.1, z.2 * h)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  rw [Measure.map_apply hm hB, secondCoordinateSlice_apply ρ A (hB.preimage hm),
    secondCoordinateSlice_apply ρ A hB]
  have he : A ×ˢ ((fun x : H => x * h) ⁻¹' B) =
      (fun z : Z × H => (z.1, z.2 * h)) ⁻¹' (A ×ˢ B) := rfl
  rw [he, ← Measure.map_apply hM (hA.prod hB), hinv]

omit [BorelSpace Z] [T2Space Z] in
theorem rightInvariant_rectangle
    [LocallyCompactSpace H] [SecondCountableTopology H]
    (ρ : Measure (Z × H)) [IsFiniteMeasureOnCompacts ρ]
    {A : Set Z} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hinv : ∀ h : H, ρ.map (fun z => (z.1, z.2 * h)) = ρ)
    (η : Measure H) [η.inv.IsHaarMeasure] :
    ∃ c : ℝ≥0, ∀ B : Set H, MeasurableSet B →
      ρ (A ×ˢ B) = (c : ℝ≥0∞) * η B := by
  let ν := secondCoordinateSlice ρ A
  let := secondCoordinateSlice_finiteOnCompacts ρ hAc
  let := secondCoordinateSlice_rightInvariant ρ A hA hinv
  have he := Measure.isMulLeftInvariant_eq_smul ν.inv η.inv
  let c : ℝ≥0 := Measure.haarScalarFactor ν.inv η.inv
  have hν : ν = c • η := by
    have hi := congrArg (fun μ : Measure H => μ.inv) he
    rw [Measure.inv_inv] at hi
    change ν = (c • η.inv).map Inv.inv at hi
    rw [Measure.map_smul c measurable_inv.aemeasurable, ← Measure.inv_def,
      Measure.inv_inv] at hi
    exact hi
  refine ⟨c, fun B hB => ?_⟩
  rw [← secondCoordinateSlice_apply ρ A hB]
  change ν B = _
  rw [hν, Measure.smul_apply]
  rfl

theorem rightInvariant_eq_product
    [LocallyCompactSpace H] [SecondCountableTopology H] [SigmaCompactSpace Z]
    (ρ : Measure (Z × H)) [IsFiniteMeasureOnCompacts ρ]
    (hinv : ∀ h : H, ρ.map (fun z => (z.1, z.2 * h)) = ρ)
    (η : Measure H) [η.inv.IsHaarMeasure]
    (K : Set H) (hK : IsCompact K) (hηK : η K = 1) :
    ρ = (firstCoordinateSlice ρ K).prod η := by
  let τ := firstCoordinateSlice ρ K
  let := firstCoordinateSlice_finiteOnCompacts ρ hK
  have : IsFiniteMeasureOnCompacts η := by
    have := Measure.IsFiniteMeasureOnCompacts.inv (μ := η.inv)
    simpa only [Measure.inv_inv] using
      (inferInstance : IsFiniteMeasureOnCompacts η.inv.inv)
  apply Eq.symm
  apply Measure.prod_eq
  intro A B hA hB
  let An : ℕ → Set Z := fun k => A ∩ compactCovering Z k
  have hAn (k : ℕ) : MeasurableSet (An k) :=
    hA.inter (isCompact_compactCovering Z k).measurableSet
  have hAnc (k : ℕ) : IsCompact (closure (An k)) :=
    (isCompact_compactCovering Z k).of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_right (isCompact_compactCovering Z k).isClosed)
  have hrect (k : ℕ) : ρ (An k ×ˢ B) = τ (An k) * η B := by
    obtain ⟨c, hc⟩ := rightInvariant_rectangle ρ (hAn k) (hAnc k) hinv η
    have ht : τ (An k) = (c : ℝ≥0∞) := by
      rw [firstCoordinateSlice_apply ρ K (hAn k), hc K hK.measurableSet, hηK, mul_one]
    rw [hc B hB, ht]
  have hmono : Monotone An := fun i j hij =>
    inter_subset_inter Subset.rfl (compactCovering_subset Z hij)
  have hunion : (⋃ k, An k) = A := by
    simp only [An, ← inter_iUnion, iUnion_compactCovering, inter_univ]
  have hprodmono : Monotone (fun k => An k ×ˢ B) := fun i j hij =>
    Set.prod_mono (hmono hij) Subset.rfl
  have hprodunion : (⋃ k, An k ×ˢ B) = A ×ˢ B := by
    rw [← iUnion_prod_const, hunion]
  calc
    ρ (A ×ˢ B) = ⨆ k, ρ (An k ×ˢ B) := by
      rw [← hprodunion, hprodmono.measure_iUnion]
    _ = ⨆ k, τ (An k) * η B := iSup_congr hrect
    _ = (⨆ k, τ (An k)) * η B := (ENNReal.iSup_mul _ _).symm
    _ = τ A * η B := by rw [← hmono.measure_iUnion, hunion]

end DukePrimeDegree

end

end OAI
