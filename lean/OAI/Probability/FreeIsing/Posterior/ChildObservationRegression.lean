import OAI.Probability.FreeIsing.Posterior.PlantedEdgeRegression
import OAI.Probability.FreeIsing.Trees.NoisyBranchSeparation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.condExp_relabel_spin_of_noisy_root_others_observable
    {d : ℕ} {theta : ℝ} {A C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [mC : MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) (c : Fin d)
    (F : (IsingSpin × A) × (∀ b : {b : Fin d // b ≠ c},
      (RootedBroadcast.BranchVertex b.val → IsingSpin) ×
        (RootedBroadcast.BranchVertex b.val → A)) → C)
    (hF : Measurable F) :
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        spinSign (z.1 (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩))) |
      mC.comap (F ∘ noisyRootOtherArray c ∘ Prod.map (relabel g) (relabel g))] =ᵐ[
        μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      fun z => theta * (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          spinSign (z.1 (g.toEquiv.symm (RootedBroadcast.root d)))) |
        mC.comap (F ∘ noisyRootOtherArray c ∘ Prod.map (relabel g) (relabel g))] z := by
  have hadj : treeAdj (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩)
      (g.toEquiv.symm (RootedBroadcast.root d)) := by
    apply (g.map_adj _ _).mp
    simp only [Equiv.apply_symm_apply]
    exact Or.inr ⟨c, rfl⟩
  have hS : Measurable (F ∘ noisyRootOtherArray c ∘
      Prod.map (relabel g) (relabel g)) :=
    hF.comp ((measurable_noisyRootOtherArray c).comp
      ((measurable_relabel g).prodMap (measurable_relabel g)))
  apply hμ.condExp_planted_spin_of_separator h0
    (Measure.infinitePi (fun _ : TreeVertex d => ν)) hadj hS
  let vc : RootedBroadcast.BranchVertex c :=
    ⟨⟨[c], List.IsChain.singleton c⟩, List.prefix_refl _⟩
  have hparent : Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A) => spinSign (p.1 vc)) :=
    measurable_spinToReal.comp ((measurable_pi_apply vc).comp measurable_fst)
  have h := (hμ.condIndepFun_relabel_noisy_root_others_branch h0 h1 ν g c).comp hF hparent
  simpa only [Function.comp_def, noisyBranchArray, Prod.map, relabel, vc] using h

end Problem367

end

end OAI
