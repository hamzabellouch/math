import OAI.Probability.FreeIsing.Stochastic.FiniteCoordinateFiltration

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

theorem cylinderEvents_eq_comap_restrict
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (D : Set ι) :
    cylinderEvents (X := X) D = MeasurableSpace.pi.comap D.domRestrict := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  simp only [cylinderEvents, iSup_subtype]
  rfl

theorem exists_coordinate_condExp_rep
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) (D : Set ι) (f : (∀ i, X i) → ℝ) :
    ∃ g : (∀ i : D, X i) → ℝ, Measurable g ∧
      μ[f | cylinderEvents D] = g ∘ D.domRestrict := by
  have hm := stronglyMeasurable_condExp (μ := μ) (f := f) (m := cylinderEvents D)
  rw [cylinderEvents_eq_comap_restrict] at hm
  obtain ⟨g, hg, h⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg.measurable, by simpa only [cylinderEvents_eq_comap_restrict] using h⟩

theorem exists_finite_coordinate_Lp_approx
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {f : (∀ i, X i) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ MemLp (g ∘ s.restrict) p μ ∧
      (∫ x, g (s.restrict x) ∂μ) = ∫ x, f x ∂μ ∧
      eLpNorm (f - g ∘ s.restrict) p μ < ε := by
  let : Encodable ι := Encodable.ofCountable ι
  let s : ℕ → Finset ι := fun n =>
    ((Set.finite_Iic n).preimage Encodable.encode_injective.injOn).toFinset
  have hs : Monotone (fun n => (s n : Set ι)) := by
    intro n m hnm i hi
    simp only [s, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_Iic] at hi ⊢
    exact hi.trans hnm
  have hex : ∀ i : ι, ∃ n, i ∈ (s n : Set ι) := by
    intro i
    refine ⟨Encodable.encode i, ?_⟩
    simp [s]
  have hlim := tendsto_Lp_coordinate_condExp μ (fun n => (s n : Set ι)) hs hex hp hpt hf
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hε)).exists
  obtain ⟨g, hg, hrep⟩ := exists_coordinate_condExp_rep μ (s n : Set ι) f
  refine ⟨s n, g, hg, ?_, ?_, ?_⟩
  · change MemLp (g ∘ (s n : Set ι).domRestrict) p μ
    rw [← hrep]
    exact MemLp.condExp hp hf
  · change (∫ x, (g ∘ (s n : Set ι).domRestrict) x ∂μ) = _
    rw [← hrep]
    exact integral_condExp cylinderEvents_le_pi
  change eLpNorm (f - g ∘ (s n : Set ι).domRestrict) p μ < ε
  rw [← hrep, eLpNorm_sub_comm]
  exact hn

end Problem367

end

end OAI
