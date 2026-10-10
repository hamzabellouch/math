import OAI.Probability.FreeIsing.Conditioning.Regrouping
import OAI.Probability.FreeIsing.Trees.NoisyBranchTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def noisyBranchArray {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (RootedBroadcast.BranchVertex c → IsingSpin) × (RootedBroadcast.BranchVertex c → A) :=
  ((fun v => z.1 v.val), fun v => z.2 v.val)

def noisyRootOtherArray {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (IsingSpin × A) × (∀ b : {b : Fin d // b ≠ c},
      (RootedBroadcast.BranchVertex b.val → IsingSpin) ×
        (RootedBroadcast.BranchVertex b.val → A)) :=
  ((z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)),
    fun b => noisyBranchArray b.val z)

theorem measurable_noisyBranchArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyBranchArray (A := A) c) := by
  unfold noisyBranchArray
  fun_prop

theorem measurable_noisyRootOtherArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyRootOtherArray (A := A) c) := by
  unfold noisyRootOtherArray noisyBranchArray
  fun_prop

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.condIndepFun_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyRootOtherArray c) (noisyBranchArray c)
      (μ.prod (Measure.infinitePi ν)) := by
  have hbranches : iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyBranchArray (A := A)) (μ.prod (Measure.infinitePi ν)) :=
    hμ.iCondIndepFun_noisy_branches h0 h1 ν
  have hothers := (condIndepFun_coordinate_others
    (fun b => measurable_noisyBranchArray (A := A) b) hbranches c).symm
  have hroot := hμ.condIndepFun_root_branch_observables h0 h1 ν id
    (fun p => ((fun b : {b : Fin d // b ≠ c} => p b.val), p c))
    measurable_id (by fun_prop)
  exact condIndepFun_prodMk_left_of_joint
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun b : {b : Fin d // b ≠ c} => noisyBranchArray b.val z) from
      Measurable.of_eval (fun b => measurable_noisyBranchArray b.val))
    (measurable_noisyBranchArray c) hroot hothers

theorem HasFreeIsingLaw.condIndepFun_relabel_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (noisyRootOtherArray c ∘ Prod.map (relabel g) (relabel g))
      (noisyBranchArray c ∘ Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (measurable_noisyRootOtherArray c) (measurable_noisyBranchArray c)
    (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
