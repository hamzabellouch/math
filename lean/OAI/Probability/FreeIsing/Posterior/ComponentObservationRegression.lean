import OAI.Probability.FreeIsing.Posterior.BranchObservationRegression
import OAI.Probability.FreeIsing.Posterior.ComponentPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.selectedPosterior_root_component
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      F (componentIndexVertex (c := c)) (RootedBroadcast.root d) =ᵐ[
        μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      fun z => theta * selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) z := by
  let := hμ.isProbabilityMeasure
  let v (u : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) → (ComponentIndex c → B) :=
    fun p u => F (p.1 (v u)) (p.2 (v u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A) => (p.1 (v u), p.2 (v u))) from by fun_prop)
  have h := hμ.condExp_root_of_noisy_branch_observable h0 h1 ν c G hG
  simpa only [selectedPosterior, selectedObservationField, Function.comp_def,
    G, noisyBranchArray, v] using h

theorem HasFreeIsingLaw.selectedPosterior_parent_childComponent
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      F (childComponentIndexVertex c a) (RootedBroadcast.branchRoot c) =ᵐ[
        μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      fun z => theta * selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (childComponentIndexVertex c a) (prefixFlip c (RootedBroadcast.branchRoot a)) z := by
  have hbase := hμ.selectedPosterior_root_component h0 h1 ν hF a
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ ν (prefixTreeAut c)
  have hp := hmp.quasiMeasurePreserving.ae_eq_comp hbase
  have hr := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := a)) (RootedBroadcast.root d) (prefixTreeAut c)
  have hc := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := a)) (RootedBroadcast.branchRoot a) (prefixTreeAut c)
  filter_upwards [hp, hr, hc] with z hp hr hc
  have h := hr.symm.trans (hp.trans (congrArg (fun x : ℝ => theta * x) hc))
  have hindex : (fun i : ComponentIndex a =>
      (prefixTreeAut c).toEquiv.symm (componentIndexVertex i)) =
        childComponentIndexVertex c a := rfl
  have hchild : (prefixTreeAut c).toEquiv.symm (RootedBroadcast.branchRoot a) =
      prefixFlip c (RootedBroadcast.branchRoot a) := rfl
  simpa only [hindex, hchild, RootedBroadcast.prefixTreeAut_symm_root] using h

end Problem367

end

end OAI
