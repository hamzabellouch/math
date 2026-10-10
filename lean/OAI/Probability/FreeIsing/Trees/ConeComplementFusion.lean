import OAI.Probability.FreeIsing.Trees.ConeSubsetFusion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem prefixFlip_mem_branch_iff {d : ℕ} (c : Fin d) (u : TreeVertex d) :
    [c] <+: (prefixFlip c u).1 ↔ ¬ [c] <+: u.1 := by
  rcases u with ⟨w, hw⟩
  cases w with
  | nil => simp [prefixFlip, prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · subst a
      cases w with
      | nil => simp [prefixFlip, prefixFlipWord]
      | cons b w =>
        have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
        simp [prefixFlip, prefixFlipWord, hcb]
    · simp [prefixFlip, prefixFlipWord, h]

theorem exists_reroot_cone_complement {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv r = ConnectedHull.root d ∧
      g.toEquiv (parentVertex r) = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∉ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  refine ⟨g.trans (prefixTreeAut c), c, ?_, ?_, ?_⟩
  · change prefixFlip c (g.toEquiv r) = _
    rw [hc]
    apply Subtype.ext
    simp [prefixFlip, prefixFlipWord, ConnectedHull.root]
  · change prefixFlip c (g.toEquiv (parentVertex r)) = _
    rw [hp]
    rfl
  · intro u
    change u ∉ cone r ↔ [c] <+: (prefixFlip c (g.toEquiv u)).1
    rw [prefixFlip_mem_branch_iff, hgeo]
end Problem367.PathSideBranches

namespace Problem367
open PathSideBranches

theorem selectedPosterior_image_relabel_ae
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (g : TreeAut d) (S : Set (TreeVertex d)) (r : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : g.toEquiv '' S → TreeVertex d) (g.toEquiv r) ∘
      Prod.map (relabel g) (relabel g) =ᵐ[P]
      selectedPosterior P F (Subtype.val : S → TreeVertex d) r := by
  have heq : Set.range (fun i : g.toEquiv '' S => g.toEquiv.symm i.1) =
      Set.range (Subtype.val : S → TreeVertex d) := by
    ext u
    constructor
    · rintro ⟨⟨v, ⟨x, hx, rfl⟩⟩, rfl⟩
      exact ⟨⟨x, hx⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨g.toEquiv x.1, ⟨x.1, x.2, rfl⟩⟩, by simp⟩
  have hfield := selectedObservationField_eq_of_range_eq F heq
  have h := selectedPosterior_relabel_ae hμ ν hF
    (Subtype.val : g.toEquiv '' S → TreeVertex d) (g.toEquiv r) g
  simpa only [selectedPosterior, hfield, Equiv.symm_apply_apply] using h

theorem HasFreeIsingLaw.selectedPosterior_child_subset_complement
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (T : Set (TreeVertex d)) (hT : T ⊆ (cone r)ᶜ) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : T → TreeVertex d) r =ᵐ[P]
      fun z => theta * selectedPosterior P F
        (Subtype.val : T → TreeVertex d) (parentVertex r) z := by
  obtain ⟨g, c, hr0, hpc, hgeo⟩ := exists_reroot_cone_complement r hr
  let q : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hq : q.1 ≠ [] := by simp [q]
  have hpq : parentVertex q = ConnectedHull.root d := by rfl
  have hsub : g.toEquiv '' T ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hT hv)
  have hbase := hμ.selectedPosterior_parent_subset_cone h0 h1 ν hF q hq
    (g.toEquiv '' T) hsub
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ ν g
  have hb := hmp.quasiMeasurePreserving.ae_eq_comp hbase
  have hleft := selectedPosterior_image_relabel_ae hμ ν hF g T r
  have hright := selectedPosterior_image_relabel_ae hμ ν hF g T (parentVertex r)
  rw [hr0] at hleft
  rw [hpc] at hright
  filter_upwards [hb, hleft, hright] with z hz hl hrz
  rw [hpq] at hz
  exact hl.symm.trans (hz.trans (congrArg (fun x : ℝ => theta * x) hrz))

theorem HasFreeIsingLaw.selected_gaussian_subset_complement_field_difference
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T U : Set (TreeVertex d)) (hS : S ⊆ cone r)
    (hT : T ⊆ (cone r)ᶜ) (hU : U ⊆ (cone r)ᶜ)
    (hp : r ∈ S) (ht : parentVertex r ∈ T) (hu : parentVertex r ∈ U) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun (V : Set (TreeVertex d)) (u : TreeVertex d) z =>
      Real.artanh (selectedPosterior P F (Subtype.val : V → TreeVertex d) u z)
    ∀ᵐ z ∂P,
      |field (S ∪ T) r z - field (S ∪ U) r z| ≤
        Real.tanh beta * |field T (parentVertex r) z - field U (parentVertex r) z| ∧
      |field (S ∪ T) r z - field (S ∪ U) r z| ≤ 2 * beta := by
  obtain ⟨g, c, hr0, hpc, hgeo⟩ := exists_reroot_cone_complement r hr
  let q : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hq : q.1 ≠ [] := by simp [q]
  have hpq : parentVertex q = ConnectedHull.root d := by rfl
  have hS' : g.toEquiv '' S ⊆ (cone q)ᶜ := by
    rintro u ⟨v, hv, rfl⟩ hbad
    exact ((hgeo v).mpr hbad) (hS hv)
  have hT' : g.toEquiv '' T ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hT hv)
  have hU' : g.toEquiv '' U ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hU hv)
  have hp' : parentVertex q ∈ g.toEquiv '' S := ⟨r, hp, hr0.trans hpq.symm⟩
  have ht' : q ∈ g.toEquiv '' T := ⟨parentVertex r, ht, hpc⟩
  have hu' : q ∈ g.toEquiv '' U := ⟨parentVertex r, hu, hpc⟩
  have hbase := hμ.selected_gaussian_subset_cone_field_difference hbeta t q hq
    (g.toEquiv '' S) (g.toEquiv '' T) (g.toEquiv '' U) hS' hT' hU' hp' ht' hu'
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hb := hmp.quasiMeasurePreserving.ae hbase
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hST := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ T) r
  have hSU := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ U) r
  have hTT := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g T (parentVertex r)
  have hUU := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g U (parentVertex r)
  filter_upwards [hb, hST, hSU, hTT, hUU] with z hz hst hsu htt huu
  have hpc' : g.toEquiv (parentVertex r) = q := hpc
  rw [hpq, ← hr0, ← hpc', ← Set.image_union, ← Set.image_union] at hz
  simp only [Function.comp_apply] at hst hsu htt huu
  dsimp only [F, PlantedSymmetry.gaussianNoiseLaw] at hst hsu htt huu hz ⊢
  simpa only [hst, hsu, htt, huu] using hz

end Problem367

end

end OAI
