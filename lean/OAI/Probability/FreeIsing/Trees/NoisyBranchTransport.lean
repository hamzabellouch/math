import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Trees.NoisyRootIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.measurePreserving_planted_relabel
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
    (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply (hμ.measurePreserving_relabel g).prod
  exact ⟨measurable_relabel g,
    Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩

theorem HasFreeIsingLaw.iCondIndepFun_relabel_noisy_branches
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun c z =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := iCondIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
    (hμ.iCondIndepFun_noisy_branches h0 h1 (fun _ => ν))
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

theorem HasFreeIsingLaw.condIndepFun_relabel_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d)
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun z => F (z.1 (g.toEquiv.symm (RootedBroadcast.root d)),
        z.2 (g.toEquiv.symm (RootedBroadcast.root d))))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val))))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from
      hF.comp (by fun_prop))
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      G (fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))) from hG.comp (by fun_prop))
    (hμ.condIndepFun_root_branch_observables h0 h1 (fun _ => ν) F G hF hG)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
