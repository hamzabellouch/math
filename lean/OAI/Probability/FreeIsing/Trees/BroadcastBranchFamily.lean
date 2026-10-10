import OAI.Probability.FreeIsing.Estimates.InfiniteBlockIndependence
import OAI.Probability.FreeIsing.Estimates.LatentFamilyIndependence
import OAI.Probability.FreeIsing.Trees.BroadcastBranchLabels

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

theorem map_branch_label_family (d : ℕ) :
    (labelMeasure d).map (fun U c => fun v : BranchVertex c => U v.val) =
      Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun _ : BranchVertex c => uniform01)) := by
  exact infinitePi_map_disjoint_family (fun _ : TreeVertex d => uniform01)
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem map_root_branch_family (d : ℕ) :
    (labelMeasure d).map (fun U => (fairSpin (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      (uniform01.map fairSpin).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun _ : BranchVertex c => uniform01))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  let F : (NonrootVertex d → ℝ) → (∀ c : Fin d, BranchVertex c → ℝ) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_fairSpin_rest d (root d)).comp measurable_id hF
  have hB : Measurable (fun U : TreeVertex d → ℝ => fairSpin (U (root d))) :=
    measurable_fairSpin.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → ℝ =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hfair : (labelMeasure d).map (fun U => fairSpin (U (root d))) =
      uniform01.map fairSpin := by
    change (labelMeasure d).map (fairSpin ∘ (fun U : TreeVertex d → ℝ => U (root d))) = _
    rw [← Measure.map_map measurable_fairSpin
      (measurable_pi_apply (X := fun _ : TreeVertex d => ℝ) (root d))]
    congr 1
    exact Measure.infinitePi_map_eval (fun _ : TreeVertex d => uniform01) (root d)
  change IndepFun (fun U : TreeVertex d → ℝ => fairSpin (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val) (labelMeasure d) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable,
    hfair, map_branch_label_family]

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem iCondIndepFun_branch_product (d : ℕ) (theta : ℝ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (Prod.fst : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ) → IsingSpin))
      measurable_fst.comap_le
      (fun c z => branchFactor theta c (z.1, z.2 c))
      ((uniform01.map fairSpin).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun _ : BranchVertex c => uniform01)))) := by
  exact iCondIndepFun_latent_infinitePi (uniform01.map fairSpin)
    (fun c : Fin d => Measure.infinitePi (fun _ : BranchVertex c => uniform01))
    (fun c => branchFactor theta c) (fun c => measurable_branchFactor theta c)

end Problem367.RootedBroadcast

end

end OAI
