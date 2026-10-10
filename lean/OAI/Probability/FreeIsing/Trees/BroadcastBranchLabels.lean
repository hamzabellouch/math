import OAI.Probability.FreeIsing.Estimates.LabelDecomposition
import OAI.Probability.FreeIsing.Trees.BroadcastLocality

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

lemma indepFun_disjoint_subarrays {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun (fun U : ι → A => fun i : S => U i.val)
      (fun U : ι → A => fun i : T => U i.val) (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => (measurable_pi_apply i).comap_le
  have h := indep_iSup_of_disjoint hle hi hST
  change Indep
    (MeasurableSpace.comap (fun U : ι → A => fun i : S => U i.val) inferInstance)
    (MeasurableSpace.comap (fun U : ι → A => fun i : T => U i.val) inferInstance)
    (Measure.infinitePi μ)
  simpa only [MeasurableSpace.comap_process_pi, iSup_subtype] using h

lemma map_disjoint_subarrays {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) (hST : Disjoint S T) :
    (Measure.infinitePi μ).map (fun U : ι → A =>
      ((fun i : S => U i.val), (fun i : T => U i.val))) =
      (Measure.infinitePi (fun i : S => μ i.val)).prod
        (Measure.infinitePi (fun i : T => μ i.val)) := by
  rw [(indepFun_disjoint_subarrays μ S T hST).map_prod_eq_prod_map_map
    ((Measurable.of_eval (fun i : S => measurable_pi_apply i.val)).aemeasurable)
    ((Measurable.of_eval (fun i : T => measurable_pi_apply i.val)).aemeasurable)]
  rw [Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

namespace RootedBroadcast

lemma branch_disjoint {d : ℕ} {c e : Fin d} (hce : c ≠ e) :
    Disjoint {v : TreeVertex d | [c] <+: v.val} {v | [e] <+: v.val} := by
  apply Set.disjoint_left.mpr
  intro v hc he
  have hprefix : [c] <+: [e] := List.prefix_of_prefix_length_le hc he (by simp)
  have heq : [c] = [e] := hprefix.eq_of_length (by simp)
  exact hce (by simpa only [List.singleton_inj] using heq)

def branchEmbedding {d : ℕ} (c : Fin d) (v : BranchVertex c) : NonrootVertex d := by
  refine ⟨v.val, ?_⟩
  intro heq
  have hlen := v.property.length_le
  rw [heq, root_val] at hlen
  simp at hlen

lemma map_branch_labels {d : ℕ} (c e : Fin d) (hce : c ≠ e) :
    (labelMeasure d).map (fun U =>
      ((fun v : BranchVertex c => U v.val), (fun v : BranchVertex e => U v.val))) =
      (Measure.infinitePi (fun _ : BranchVertex c => uniform01)).prod
        (Measure.infinitePi (fun _ : BranchVertex e => uniform01)) :=
  map_disjoint_subarrays (fun _ : TreeVertex d => uniform01) _ _ (branch_disjoint hce)

lemma map_root_two_branches {d : ℕ} (c e : Fin d) (hce : c ≠ e) :
    (labelMeasure d).map (fun U => (fairSpin (U (root d)),
      ((fun v : BranchVertex c => U v.val), (fun v : BranchVertex e => U v.val)))) =
      (uniform01.map fairSpin).prod
        ((Measure.infinitePi (fun _ : BranchVertex c => uniform01)).prod
          (Measure.infinitePi (fun _ : BranchVertex e => uniform01))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  let F : (NonrootVertex d → ℝ) → (BranchVertex c → ℝ) × (BranchVertex e → ℝ) :=
    fun Y => ((fun v => Y (branchEmbedding c v)), (fun v => Y (branchEmbedding e v)))
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_fairSpin_rest d (root d)).comp measurable_id hF
  have hB : Measurable (fun U : TreeVertex d → ℝ => fairSpin (U (root d))) :=
    measurable_fairSpin.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → ℝ =>
      ((fun v : BranchVertex c => U v.val), (fun v : BranchVertex e => U v.val))) := by fun_prop
  have hfair : (labelMeasure d).map (fun U => fairSpin (U (root d))) =
      uniform01.map fairSpin := by
    change (labelMeasure d).map (fairSpin ∘ (fun U : TreeVertex d → ℝ => U (root d))) = _
    rw [← Measure.map_map measurable_fairSpin
      (measurable_pi_apply (X := fun _ : TreeVertex d => ℝ) (root d))]
    congr 1
    exact Measure.infinitePi_map_eval (fun _ : TreeVertex d => uniform01) (root d)
  change IndepFun (fun U : TreeVertex d → ℝ => fairSpin (U (root d)))
    (fun U => ((fun v : BranchVertex c => U v.val), (fun v : BranchVertex e => U v.val)))
    (labelMeasure d) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable,
    hfair, map_branch_labels c e hce]

end RootedBroadcast
end Problem367

end

end OAI
