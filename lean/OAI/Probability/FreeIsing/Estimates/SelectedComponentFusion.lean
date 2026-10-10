import OAI.Probability.FreeIsing.Posterior.FusionSup
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorField
import OAI.Probability.FreeIsing.Trees.RootComponentAttenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem HasFreeIsingLaw.condIndepFun_selected_outside_component
    {d : ℕ} {theta : ℝ} {A B ι : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (v : ι → TreeVertex d) (hv : ∀ i, ¬ [c] <+: (v i).val) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun p i => F (p.1 (v i)) (p.2 (v i)))
      (fun p i => F (p.1 (componentIndexVertex (c := c) i))
        (p.2 (componentIndexVertex i)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let G : NoisyRootOtherData A c → (ι → B) := fun p i =>
    F (noisyRootOtherDecode c p ⟨v i, hv i⟩).1
      (noisyRootOtherDecode c p ⟨v i, hv i⟩).2
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (measurable_noisyRootOtherDecode c ⟨v i, hv i⟩)
  let w (i : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex i, by simp [componentIndexVertex, componentVertex]⟩
  let H : ((RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → (ComponentIndex c → B) :=
    fun p i => F (p.1 (w i)) (p.2 (w i))
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A) => (p.1 (w i), p.2 (w i))) from by fun_prop)
  have hGcomp : G ∘ noisyRootOtherArray c =
      fun p i => F (p.1 (v i)) (p.2 (v i)) := by
    funext p i
    change F (noisyRootOtherDecode c (noisyRootOtherArray c p) ⟨v i, hv i⟩).1
      (noisyRootOtherDecode c (noisyRootOtherArray c p) ⟨v i, hv i⟩).2 = _
    rw [noisyRootOtherDecode_array]
  have h := (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c).comp hG hH
  rw [hGcomp] at h
  exact h

theorem HasFreeIsingLaw.selected_gaussian_outside_component_fusion
    {d : ℕ} {ι : Type*} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) (v : ι → TreeVertex d)
    (hv : ∀ i, ¬ [c] <+: (v i).val)
    (hr : RootedBroadcast.root d ∈ Set.range v) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    P[fun p => spinSign (p.1 (RootedBroadcast.root d)) |
      selectedObservationField F v ⊔
        selectedObservationField F (componentIndexVertex (c := c))] =ᵐ[P]
      fun p => binaryFusion (selectedPosterior P F v (RootedBroadcast.root d) p)
        (Real.tanh beta * ComponentSignalAttenuation.posteriorMean μ c t p) := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let X := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i => F (p.1 (v i)) (p.2 (v i))
  let Y := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i => F (p.1 (componentIndexVertex (c := c) i)) (p.2 (componentIndexVertex i))
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (p.1 (v i), p.2 (v i))) from by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (p.1 (componentIndexVertex (c := c) i), p.2 (componentIndexVertex i))) from by fun_prop)
  have hInd := hμ.condIndepFun_selected_outside_component
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) hF c v hv
  have hreg : P[fun p => spinSign (p.1 (RootedBroadcast.root d)) |
      selectedObservationField F (componentIndexVertex (c := c))] =ᵐ[P]
      fun p => Real.tanh beta * ComponentSignalAttenuation.posteriorMean μ c t p :=
    hμ.selectedPosterior_root_component (Real.neg_one_lt_tanh beta).le
      (Real.tanh_lt_one beta).le (gaussianReal 0 t) hF c
  have hL : ∀ᵐ p ∂P,
      |selectedPosterior P F v (RootedBroadcast.root d) p| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t v
      (RootedBroadcast.root d) hr] with p hp
    exact abs_lt.mpr hp.1
  have hR : ∀ᵐ p ∂P,
      |(P[fun p => spinSign (p.1 (RootedBroadcast.root d)) |
        selectedObservationField F (componentIndexVertex (c := c))]) p| < 1 := by
    filter_upwards [hreg, ComponentSignalAttenuation.posteriorMean_abs_le_one μ c t]
      with p hp hq
    rw [hp, abs_mul]
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg (Real.tanh beta))).trans_lt
      (by simpa using Real.abs_tanh_lt_one beta)
  have h := condExp_spin_comap_sup_eq_binaryFusion
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst) hX hY
    (hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) _) hInd hL hR
  filter_upwards [h, hreg] with p hp hregp
  exact hp.trans (congrArg (binaryFusion (selectedPosterior P F v
    (RootedBroadcast.root d) p)) hregp)

end Problem367

end

end OAI
