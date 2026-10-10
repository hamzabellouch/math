import OAI.Probability.FreeIsing.Posterior.ComponentPosteriorStationarity
import OAI.Probability.FreeIsing.Trees.NoisyBranchTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.iCondIndepFun_child_component_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : Fin d => fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a => F (p.1 (childComponentIndexVertex c a u))
          (p.2 (childComponentIndexVertex c a u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G (a : Fin d) : (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A) → (ComponentIndex a → B) :=
    fun p u => F (p.1 (v a u)) (p.2 (v a u))
  have hG (a : Fin d) : Measurable (G a) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A) => (p.1 (v a u), p.2 (v a u))) by fun_prop)
  have h := (hμ.iCondIndepFun_relabel_noisy_branches h0 h1 ν (prefixTreeAut c)).comp G hG
  exact h

theorem HasFreeIsingLaw.iCondIndepFun_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : {a : Fin d // c ≠ a} =>
        fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a.1 => F (p.1 (childComponentIndexVertex c a.1 u))
          (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  exact Kernel.iIndepFun.precomp Subtype.val_injective
    (hμ.iCondIndepFun_child_component_observations h0 h1 ν hF c)

theorem HasFreeIsingLaw.condIndepFun_own_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        F (p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))) (p.2 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun a : {a : Fin d // c ≠ a} => fun u : ComponentIndex a.1 =>
          F (p.1 (childComponentIndexVertex c a.1 u))
            (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A)) →
      (∀ a : {a : Fin d // c ≠ a}, ComponentIndex a.1 → B) :=
    fun p a u => F ((p a.1).1 (v a.1 u)) ((p a.1).2 (v a.1 u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A)) =>
          ((p a.1).1 (v a.1 u), (p a.1).2 (v a.1 u))) by fun_prop)
  have h := hμ.condIndepFun_relabel_root_branch_observables h0 h1 ν (prefixTreeAut c)
    (Function.uncurry F) G hF hG
  exact h

end Problem367

end

end OAI
