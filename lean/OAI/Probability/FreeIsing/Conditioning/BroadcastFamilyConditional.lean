import OAI.Probability.FreeIsing.Conditioning.FamilyConditionalPullback
import OAI.Probability.FreeIsing.Trees.BroadcastBranchFamily

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem iCondIndepFun_factor_branches (d : ℕ) (theta : ℝ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ => fairSpin (U (root d))))
      (measurable_fairSpin.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => fun v : BranchVertex c => factor theta U v.val)
      (labelMeasure d) := by
  let e : (TreeVertex d → ℝ) → IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ) :=
    fun U => (fairSpin (U (root d)), fun c v => U v.val)
  let ν : Measure (IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ)) :=
    (uniform01.map fairSpin).prod (Measure.infinitePi (fun c : Fin d =>
      Measure.infinitePi (fun _ : BranchVertex c => uniform01)))
  have he : MeasurePreserving e (labelMeasure d) ν :=
    ⟨(measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (by fun_prop), map_root_branch_family d⟩
  have hbase := iCondIndepFun_branch_product d theta
  have hpull := iCondIndepFun_comp_measurePreserving (labelMeasure d) ν e he
    ((inferInstance : MeasurableSpace IsingSpin).comap Prod.fst)
    measurable_fst.comap_le
    (fun c : Fin d => show Measurable
      (fun z : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ) =>
        branchFactor theta c (z.1, z.2 c)) from
      (measurable_branchFactor theta c).comp
        (measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd))) hbase
  have hfun : (fun c : Fin d =>
      (fun z : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ) =>
        branchFactor theta c (z.1, z.2 c)) ∘ e) =
      (fun c U => fun v : BranchVertex c => factor theta U v.val) := by
    funext c U
    exact (factor_branch_representation theta c U).symm
  rw [hfun] at hpull
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

end Problem367.RootedBroadcast

end

end OAI
