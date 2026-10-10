import OAI.Probability.SLE.MainReduction

namespace OAI

/-!
The deterministic and integration steps in the upper-cover arguments of
the two exact-gauge manuscripts. These lemmas do not assume a Hausdorff
upper bound: they pass from actual shrinking covers to that bound.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- Cover costs control the Hausdorff limit even when they do not converge. -/
theorem hausdorff_le_liminf_cover_cost
    (h : ℝ → ℝ) (hh : IsGauge h) (E : Set ℂ)
    (U : ℕ → ℕ → Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hcover : ∀ n, E ⊆ ⋃ j, U n j)
    (hdiam : ∀ n j, ediam (U n j) ≤ δ n) :
    hausdorffGauge h E ≤
      liminf (fun n => ∑' j, extendedGauge h (ediam (U n j))) atTop := by
  rw [source_gauge_cover_formula h hh]
  refine iSup_le fun r => iSup_le fun hr => ?_
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards [hδ.eventually (gt_mem_nhds hr)] with n hn
  exact iInf_le_of_le (U n) (iInf_le_of_le (hcover n)
    (iInf_le_of_le (fun j => (hdiam n j).trans hn.le) le_rfl))

/-- Fatou's lemma for measurable costs of actual covers, with a limiting
expectation bound rather than an assumption about the target measure. -/
theorem expected_hausdorff_le_of_shrinking_covers
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (hh : IsGauge h) (E : Ω → Set ℂ)
    (U : ℕ → Ω → ℕ → Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hcover : ∀ᵐ ω ∂P, ∀ n, E ω ⊆ ⋃ j, U n ω j)
    (hdiam : ∀ᵐ ω ∂P, ∀ n j, ediam (U n ω j) ≤ δ n)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => ∑' j, extendedGauge h (ediam (U n ω j))) P)
    (C : ℝ≥0∞)
    (hcost : liminf (fun n => ∫⁻ ω,
      ∑' j, extendedGauge h (ediam (U n ω j)) ∂P) atTop ≤ C) :
    (∫⁻ ω, hausdorffGauge h (E ω) ∂P) ≤ C := by
  calc
    _ ≤ ∫⁻ ω, liminf (fun n => ∑' j,
        extendedGauge h (ediam (U n ω j))) atTop ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hcover, hdiam] with ω hc hd
      exact hausdorff_le_liminf_cover_cost h hh (E ω)
        (fun n => U n ω) δ hδ hc hd
    _ ≤ liminf (fun n => ∫⁻ ω,
        ∑' j, extendedGauge h (ediam (U n ω j)) ∂P) atTop :=
      lintegral_liminf_le' hmeas
    _ ≤ C := hcost

/-- Disjoint candidate sets are all paid for by the same spatial measure. -/
theorem disjoint_cover_charge {ι : Type*} (I : Finset ι)
    (ν : Measure ℂ) (D : ι → Set ℂ) (A : Set ℂ)
    (hdisj : (I : Set ι).PairwiseDisjoint D)
    (hmeas : ∀ i ∈ I, MeasurableSet (D i))
    (hsub : ∀ i ∈ I, D i ⊆ A)
    (cost : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcost : ∀ i ∈ I, cost i ≤ C * ν (D i)) :
    ∑ i ∈ I, cost i ≤ C * ν A := by
  calc
    _ ≤ ∑ i ∈ I, C * ν (D i) := Finset.sum_le_sum hcost
    _ = C * ∑ i ∈ I, ν (D i) := (Finset.mul_sum I _ C).symm
    _ = C * ν (⋃ i ∈ I, D i) := by
      rw [measure_biUnion_finset hdisj hmeas]
    _ ≤ C * ν A := mul_le_mul' le_rfl (measure_mono (iUnion₂_subset hsub))

/-- Continuity from below retains a uniform expectation bound as both the
time cutoff and the distance from the real boundary are removed. -/
theorem expected_measure_iUnion_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Measure X) (E : ℕ → Ω → Set X)
    (hmono : ∀ ω, Monotone (fun n => E n ω))
    (hmeas : ∀ n, AEMeasurable (fun ω => ν (E n ω)) P)
    (C : ℝ≥0∞) (hbound : ∀ n, (∫⁻ ω, ν (E n ω) ∂P) ≤ C) :
    (∫⁻ ω, ν (⋃ n, E n ω) ∂P) ≤ C := by
  simp_rw [Monotone.measure_iUnion (hmono _)]
  rw [lintegral_iSup' hmeas (Eventually.of_forall fun ω i j hij =>
    measure_mono (hmono ω hij))]
  exact iSup_le hbound

/-- Adding a set contained in a fixed null boundary costs no measure. -/
theorem measure_inter_eq_interior_of_null_boundary
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (E A H : Set X)
    (hboundary : ν (E ∩ A ∩ Hᶜ) = 0) :
    ν (E ∩ A) = ν (E ∩ A ∩ H) := by
  apply le_antisymm
  · calc
      ν (E ∩ A) = ν ((E ∩ A ∩ H) ∪ (E ∩ A ∩ Hᶜ)) := by
        congr 1
        ext x
        simp only [mem_inter_iff, mem_union, mem_compl_iff]
        tauto
      _ ≤ ν (E ∩ A ∩ H) + ν (E ∩ A ∩ Hᶜ) := measure_union_le _ _
      _ = ν (E ∩ A ∩ H) := by rw [hboundary, add_zero]
  · exact measure_mono inter_subset_left

end SLEExactGauge

end

end OAI
