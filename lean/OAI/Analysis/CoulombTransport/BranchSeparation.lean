import OAI.Analysis.CoulombTransport.BranchCoupling
import OAI.Analysis.CoulombTransport.CompactSeparation
import OAI.Analysis.CoulombTransport.CoulombEstimates

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- The central compact set and its four transported copies. -/
def components (K : Set E3) (H : Fin 4 → E3 → E3) : Fin 5 → Set E3 :=
  Fin.cases K (fun i => H i '' K)

lemma compact_components {K : Set E3} (hK : IsCompact K)
    {H : Fin 4 → E3 → E3} (hH : ∀ i, ContinuousOn (H i) K) :
    ∀ i, IsCompact (components K H i) := by
  intro i
  exact Fin.cases hK (fun j => hK.image_of_continuousOn (hH j)) i

lemma measurableSet_separated (eta : ℝ) :
    MeasurableSet {t : Triple | CoulombEstimates.Separated eta t} := by
  have h12 : Measurable (fun t : Triple => dist t.1 t.2.1) :=
    measurable_fst.dist (measurable_fst.comp measurable_snd)
  have h13 : Measurable (fun t : Triple => dist t.1 t.2.2) :=
    measurable_fst.dist (measurable_snd.comp measurable_snd)
  have h23 : Measurable (fun t : Triple => dist t.2.1 t.2.2) :=
    (measurable_fst.comp measurable_snd).dist (measurable_snd.comp measurable_snd)
  exact (measurableSet_le measurable_const h12).inter
    ((measurableSet_le measurable_const h13).inter (measurableSet_le measurable_const h23))

/-- Uniform separation for the actual cyclic two-branch coupling follows from
compactness and disjointness of its five component sets. -/
theorem exists_ae_separated_branchCoupling
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t := by
  obtain ⟨eta, heta, hsep⟩ := exists_uniform_compact_separation
    (components K H) (compact_components hK hcont) hdisjoint
  have hcentral (i : Fin 4) {x : E3} (hx : x ∈ K) : eta ≤ dist x (H i x) := by
    exact hsep 0 i.succ (Fin.succ_ne_zero i).symm x hx (H i x) (mem_image_of_mem _ hx)
  have houter (i j : Fin 4) (hij : i ≠ j) {x : E3} (hx : x ∈ K) :
      eta ≤ dist (H i x) (H j x) := by
    exact hsep i.succ j.succ (by simpa using hij) (H i x) (mem_image_of_mem _ hx)
      (H j x) (mem_image_of_mem _ hx)
  refine ⟨eta, heta, ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
    (measurableSet_separated eta) ?_ ?_ ?_⟩
  · intro x y z h
    exact ⟨h.2.2, by simpa only [dist_comm] using h.1,
      by simpa only [dist_comm] using h.2.1⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 0 hx, hcentral 1 hx, houter 0 1 (by decide) hx⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 2 hx, hcentral 3 hx, houter 2 3 (by decide) hx⟩

/-- The branch marginal is concentrated on the union of the central compact
set and its four images. -/
theorem ae_mem_branchMarginal_components
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3),
      x ∈ ⋃ i, components K H i := by
  have hcompact : IsCompact (⋃ i, components K H i) :=
    isCompact_iUnion (compact_components hK hcont)
  have hcentral : ∀ᵐ x ∂nu, x ∈ ⋃ i, components K H i := by
    filter_upwards [hnu] with x hx
    exact mem_iUnion.mpr ⟨0, hx⟩
  have houter (i : Fin 4) : ∀ᵐ x ∂Measure.map (H i) nu,
      x ∈ ⋃ j, components K H j := by
    apply (ae_map_iff (hH i).aemeasurable hcompact.measurableSet).mpr
    filter_upwards [hnu] with x hx
    exact mem_iUnion.mpr ⟨i.succ, mem_image_of_mem _ hx⟩
  unfold branchMarginal
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure (c := (1 / 3 : ℝ≥0∞)) hcentral
  · apply Measure.ae_smul_measure
    simp only [ae_add_measure_iff]
    exact ⟨⟨⟨houter 0, houter 1⟩, houter 2⟩, houter 3⟩

/-- The compact support and uniformly separated optimizer hypotheses needed
for finite Monge approximation hold for the explicit branch construction. -/
theorem compact_support_and_separation
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    (∃ S : Set E3, IsCompact S ∧
      ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ S) ∧
    (∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t) := by
  exact ⟨⟨⋃ i, components K H i, isCompact_iUnion (compact_components hK hcont),
    ae_mem_branchMarginal_components hK hnu hH hcont⟩,
    exists_ae_separated_branchCoupling hK hnu hH hcont hdisjoint⟩

/-- A compact subcomponent retains disjointness of the larger local domains. -/
lemma disjoint_components_mono {K B : Set E3} (hKB : K ⊆ B)
    {H : Fin 4 → E3 → E3}
    (hB : Pairwise (fun i j => Disjoint (components B H i) (components B H j))) :
    Pairwise (fun i j => Disjoint (components K H i) (components K H j)) := by
  have hsub : ∀ i, components K H i ⊆ components B H i := by
    intro i
    exact Fin.cases hKB (fun j => image_mono hKB) i
  intro i j hij
  exact (hB hij).mono (hsub i) (hsub j)

/-- Under the compact disjoint-component hypotheses, the explicit candidate
already has finite cost, before applying any dual certificate. -/
theorem finite_cost_branchCoupling
    {nu : Measure E3} [IsProbabilityMeasure nu] {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have := isProbabilityMeasure_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  obtain ⟨eta, heta, hae⟩ := exists_ae_separated_branchCoupling hK hnu hH hcont hdisjoint
  exact CoulombEstimates.lintegral_coulombCost_lt_top_of_ae_separated _ heta hae

end Problem356.BranchSeparation

end

end OAI
