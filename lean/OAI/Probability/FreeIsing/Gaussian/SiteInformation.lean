import OAI.Probability.FreeIsing.Estimates.ComponentFusionRecurrence
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem component_or_flipped_component {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    v ∈ Set.range (componentIndexVertex (c := c)) ∨
      v ∈ Set.range (fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)) := by
  by_cases h : [c] <+: v.1
  · left
    apply mem_range_componentIndexVertex.mpr
    obtain ⟨w, hw⟩ := h
    exact ⟨w, by simpa using hw.symm⟩
  · right
    have hf := (RootedBroadcast.prefix_flip_iff_not_prefix c v).mpr h
    obtain ⟨w, hw⟩ := hf
    have hmem : prefixFlip c v ∈ Set.range (componentIndexVertex (c := c)) :=
      mem_range_componentIndexVertex.mpr ⟨w, by simpa using hw.symm⟩
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    change prefixFlip c (componentIndexVertex u) = v
    rw [hu, prefixFlip_twice]

theorem selectedObservationField_eq_component_sup_flip
    {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (c : Fin d) :
    selectedObservationField F id =
      selectedObservationField F (fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)) ⊔
      selectedObservationField F (componentIndexVertex (c := c)) := by
  apply le_antisymm
  · simp only [selectedObservationField, MeasurableSpace.comap_process_pi, id_eq]
    apply iSup_le
    intro v
    rcases component_or_flipped_component c v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact le_sup_of_le_right (le_iSup_of_le u le_rfl)
    · exact le_sup_of_le_left (le_iSup_of_le u le_rfl)
  · apply sup_le
    · apply selectedObservationField_le_of_range_subset F
      intro v hv
      exact ⟨v, rfl⟩
    · apply selectedObservationField_le_of_range_subset F
      intro v hv
      exact ⟨v, rfl⟩

theorem HasFreeIsingLaw.condIndepFun_component_flip_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => fun u : ComponentIndex c => F
        (z.1 (prefixFlip c (componentIndexVertex u))) (z.2 (prefixFlip c (componentIndexVertex u))))
      (fun z => fun u : ComponentIndex c => F (z.1 (componentIndexVertex u)) (z.2 (componentIndexVertex u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let v (u : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G (p : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) :=
    fun u : ComponentIndex c => F (p.1 (v u)) (p.2 (v u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) => (p.1 (v u), p.2 (v u))) by fun_prop)
  have h := (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c).comp
    (hG.comp (measurable_decodeFlippedBranch c)) hG
  simpa only [Function.comp_def, G, decodeFlippedBranch, noisyRootOtherDecode_array,
    RootedBroadcast.flipBranchToComplement_val, noisyBranchArray, v] using h

theorem HasFreeIsingLaw.gaussian_root_information_le_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t
      (RootedBroadcast.root d) z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c := by
  let := hμ.isProbabilityMeasure
  let mΩ : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := inferInstance
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  let r := RootedBroadcast.root d
  let w := fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)
  let mL := selectedObservationField F w
  let mR := selectedObservationField F (componentIndexVertex (c := c))
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := mΩ
  let S (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := z.1 r
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hS : Measurable S := (measurable_pi_apply r).comp measurable_fst
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθ1 := Real.tanh_lt_one beta
  have hθlo : -1 ≤ Real.tanh beta := by linarith
  have hfair (s : IsingSpin) : ρ {z | S z = s} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r s
  have hL : ∀ᵐ z ∂ρ, |ρ[fun z => spinSign (S z) | mL] z| < 1 := by
    have hr : r ∈ Set.range w := by
      refine ⟨⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩, ?_⟩
      exact RootedBroadcast.prefixFlip_branchRoot c
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hb t w r hr] with z hz
    exact abs_lt.mpr hz.1
  have hreg := hμ.selectedPosterior_root_component hθlo hθ1.le (gaussianReal 0 t) hF c
  have hR : ∀ᵐ z ∂ρ, |ρ[fun z => spinSign (S z) | mR] z| < 1 := by
    filter_upwards [hreg, selectedPosterior_abs_le_one ρ F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)] with z hz hz1
    change |selectedPosterior ρ F (componentIndexVertex (c := c)) r z| < 1
    change selectedPosterior ρ F (componentIndexVertex (c := c)) r z =
      Real.tanh beta * selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z at hz
    rw [hz, abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left hz1 hθ0).trans_lt (by simpa using hθ1)
  have hCI := hμ.condIndepFun_component_flip_observations hθlo hθ1.le (gaussianReal 0 t) hF c
  have hInd (s : IsingSpin) : Indep mL mR (cond ρ {z | S z = s}) := by
    exact indepFun_cond_fiber_of_condIndepFun hS
      (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun u : ComponentIndex c => F (z.1 (w u)) (z.2 (w u))) from
        Measurable.of_eval (fun u => hF.comp (show Measurable
          (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
            (z.1 (w u), z.2 (w u))) by fun_prop)))
      (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun u : ComponentIndex c => F (z.1 (componentIndexVertex u)) (z.2 (componentIndexVertex u))) from
        Measurable.of_eval (fun u => hF.comp (show Measurable
          (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
            (z.1 (componentIndexVertex u), z.2 (componentIndexVertex u))) by fun_prop))) hCI s
  have hsym := hμ.selected_gaussian_posteriorLaw_neg_invariant t t
    (componentIndexVertex (c := c)) r
  have hsum := spinInformation_sup_le_add (selectedObservationField_le hF w)
    (selectedObservationField_le hF (componentIndexVertex (c := c))) hS hL hR hfair hInd hsym
  have hfield := selectedObservationField_eq_component_sup_flip F c
  change selectedObservationField F id = mL ⊔ mR at hfield
  rw [← hfield] at hsum
  have hleft : spinInformation ρ S mL = gaussianComponentInformation μ t c := by
    have h := selectedPosterior_secondMoment_relabel hμ (gaussianReal 0 t) hF
      (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) (prefixTreeAut c)
    rw [RootedBroadcast.prefixTreeAut_symm_branchRoot] at h
    exact h.symm
  have hright : spinInformation ρ S mR =
      (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c := by
    have h := integral_congr_ae (hreg.fun_comp (fun x : ℝ => x ^ 2))
    simp only [Function.comp_apply, mul_pow, integral_const_mul] at h
    exact h
  rw [hleft, hright] at hsum
  change (∫ z, (PlantedSymmetry.posteriorMagnetization ρ t r z) ^ 2 ∂ρ) ≤ _ at hsum
  nlinarith [hsum]

theorem HasFreeIsingLaw.gaussian_site_information_le_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) (v : TreeVertex d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c := by
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  obtain ⟨g, hg⟩ := exists_treeAut_map (RootedBroadcast.root d) v
  have hroot : g.toEquiv.symm v = RootedBroadcast.root d := by rw [← hg]; simp
  have hregion : Set.range (fun i : TreeVertex d => g.toEquiv.symm (id i)) = Set.range id := by
    rw [Set.range_id]
    exact Set.range_eq_univ.mpr g.toEquiv.symm.surjective
  have h := selectedPosterior_identDistrib_of_range_relabel hμ (gaussianReal 0 t)
    hF id id v (RootedBroadcast.root d) g hregion hroot
  have heq := (h.comp (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)).integral_eq
  change (∫ z, (PlantedSymmetry.posteriorMagnetization
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
    ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) = _ at heq
  rw [heq]
  exact hμ.gaussian_root_information_le_component hb t c

theorem HasFreeIsingLaw.gaussian_site_critical_information_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      ((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt (t : ℝ) := by
  let c : Fin d := ⟨0, by omega⟩
  have h := (hμ.gaussian_site_information_le_component hb t c v).trans
    (mul_le_mul_of_nonneg_left
      (hμ.gaussian_component_critical_information_upper hd hb hcritical t ht c)
      (by positivity : 0 ≤ 1 + (Real.tanh beta) ^ 2))
  simpa only [mul_assoc] using h

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_critical_secondMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ z, (infiniteGibbsSpinMean beta v (PlantedSymmetry.observation t z)) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      ((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt (t : ℝ) := by
  have hEq := integral_congr_ae
    ((hμ.infiniteGibbsSpinMean_eq_posterior t v).fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hEq
  rw [hEq]
  exact hμ.gaussian_site_critical_information_upper hd hb hcritical t ht v

end Problem367

end

end OAI
