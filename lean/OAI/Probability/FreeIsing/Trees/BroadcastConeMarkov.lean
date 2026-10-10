import OAI.Probability.FreeIsing.Trees.BroadcastBlockIndependence
import OAI.Probability.FreeIsing.Trees.BroadcastConeLocality
import OAI.Probability.FreeIsing.Trees.BroadcastOutsideCone

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

private lemma nonroot_of_prefix {d : ℕ} {b w : TreeVertex d}
    (hb : b.val ≠ []) (hw : b.val <+: w.val) : w ≠ root d := by
  intro h
  rw [h, root_val] at hw
  exact hb (List.prefix_nil.mp hw)

private lemma parent_outside_cone {d : ℕ} (b : TreeVertex d) (hb : b.val ≠ []) :
    ¬ b.val <+: (parent b).val := by
  intro h
  have hl := h.length_le
  change b.val.length ≤ (parentVertex b).val.length at hl
  rw [parentVertex_length] at hl
  have hp : 0 < b.val.length := List.length_pos_iff.mpr hb
  omega

theorem condIndepFun_outside_cone_given_parent {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun
      (MeasurableSpace.comap (fun U => factor theta U (parent b)) inferInstance)
      (((measurable_pi_apply (parent b)).comp (measurable_factor d theta)).comap_le)
      (fun U => fun v : OutsideConeVertex b => factor theta U v.val)
      (fun U => fun v : DescendantVertex b => factor theta U v.val)
      (labelMeasure d) := by
  let S : Set (NonrootVertex d) := {w | ¬ b.val <+: w.val.val}
  let T : Set (NonrootVertex d) := {w | b.val <+: w.val.val}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs ht)
  let outsideIndex : OutsideConeNonroot b → S := fun w =>
    ⟨⟨w.val, fun h => w.property.1 ((eq_root_iff w.val).mp h)⟩, w.property.2⟩
  let baseIndex : T := ⟨⟨b, nonroot_of_prefix hb (List.prefix_refl _)⟩,
    List.prefix_refl _⟩
  let strictIndex : StrictDescendantVertex b → T := fun w =>
    ⟨⟨w.val, nonroot_of_prefix hb w.property.1⟩, w.property.1⟩
  let a : OutsideConeVertex b := ⟨parent b, parent_outside_cone b hb⟩
  let F : IsingSpin × (S → ℝ) → OutsideConeVertex b → IsingSpin := fun p =>
    outsideConeFactor theta b a (p.1, fun w => p.2 (outsideIndex w))
  let G : IsingSpin × (T → ℝ) → DescendantVertex b → IsingSpin := fun p =>
    coneFactor theta b (spinMul (edgeNoise theta (p.2 baseIndex)) p.1,
      fun w => p.2 (strictIndex w))
  have hF : Measurable F := by
    apply (measurable_outsideConeFactor theta b a).comp
    exact measurable_fst.prodMk
      (Measurable.of_eval
        (fun vertex => (measurable_pi_apply (outsideIndex vertex)).comp measurable_snd))
  have hG : Measurable G := by
    apply (measurable_coneFactor theta b).comp
    apply Measurable.prodMk
    · exact measurable_spinMul.comp
        (((measurable_edgeNoise theta).comp
          ((measurable_pi_apply baseIndex).comp measurable_snd)).prodMk measurable_fst)
    · exact Measurable.of_eval
        (fun vertex => (measurable_pi_apply (strictIndex vertex)).comp measurable_snd)
  have hFrep : ∀ U : TreeVertex d → ℝ,
      F (factor theta U (parent b), fun i : S => U i.val.val) =
        fun v : OutsideConeVertex b => factor theta U v.val := by
    intro U
    exact (factor_outsideCone_representation theta b a U).symm
  have hGrep : ∀ U : TreeVertex d → ℝ,
      G (factor theta U (parent b), fun i : T => U i.val.val) =
        fun v : DescendantVertex b => factor theta U v.val := by
    intro U
    rw [factor_cone_representation]
    change coneFactor theta b
      (spinMul (edgeNoise theta (U b)) (factor theta U (parent b)),
        fun w : StrictDescendantVertex b => U w.val) =
      coneFactor theta b
        (factor theta U b, fun w : StrictDescendantVertex b => U w.val)
    have hspin : factor theta U b =
        spinMul (edgeNoise theta (U b)) (factor theta U (parent b)) := by
      change ofNoise (inputNoise theta U) b = _
      rw [ofNoise_nonroot _ b hb]
      simp only [inputNoise, ite_eq_right hb]
      rfl
    rw [hspin]
  have h := condIndepFun_factor_disjoint_blocks theta (parent b) S T hST F G hF hG
  simpa only [hFrep, hGrep] using h

theorem condIndepFun_outside_cone_given_child {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun
      (MeasurableSpace.comap (fun U => factor theta U b) inferInstance)
      (((measurable_pi_apply b).comp (measurable_factor d theta)).comap_le)
      (fun U => fun v : OutsideConeVertex b => factor theta U v.val)
      (fun U => fun v : DescendantVertex b => factor theta U v.val)
      (labelMeasure d) := by
  let S : Set (NonrootVertex d) := {w | ¬ (b.val <+: w.val.val ∧ w.val ≠ b)}
  let T : Set (NonrootVertex d) := {w | b.val <+: w.val.val ∧ w.val ≠ b}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs ht)
  let outsideIndex : OutsideConeNonroot b → S := fun w =>
    ⟨⟨w.val, fun h => w.property.1 ((eq_root_iff w.val).mp h)⟩,
      fun h => w.property.2 h.1⟩
  let baseIndex : S := ⟨⟨b, nonroot_of_prefix hb (List.prefix_refl _)⟩,
    fun h => h.2 rfl⟩
  let strictIndex : StrictDescendantVertex b → T := fun w =>
    ⟨⟨w.val, nonroot_of_prefix hb w.property.1⟩, w.property⟩
  let a : OutsideConeVertex b := ⟨parent b, parent_outside_cone b hb⟩
  let F : IsingSpin × (S → ℝ) → OutsideConeVertex b → IsingSpin := fun p =>
    outsideConeFactor theta b a
      (spinMul (edgeNoise theta (p.2 baseIndex)) p.1,
        fun w => p.2 (outsideIndex w))
  let G : IsingSpin × (T → ℝ) → DescendantVertex b → IsingSpin := fun p =>
    coneFactor theta b (p.1, fun w => p.2 (strictIndex w))
  have hF : Measurable F := by
    apply (measurable_outsideConeFactor theta b a).comp
    apply Measurable.prodMk
    · exact measurable_spinMul.comp
        (((measurable_edgeNoise theta).comp
          ((measurable_pi_apply baseIndex).comp measurable_snd)).prodMk measurable_fst)
    · exact Measurable.of_eval
        (fun vertex => (measurable_pi_apply (outsideIndex vertex)).comp measurable_snd)
  have hG : Measurable G := by
    apply (measurable_coneFactor theta b).comp
    exact measurable_fst.prodMk
      (Measurable.of_eval
        (fun vertex => (measurable_pi_apply (strictIndex vertex)).comp measurable_snd))
  have hFrep : ∀ U : TreeVertex d → ℝ,
      F (factor theta U b, fun i : S => U i.val.val) =
        fun v : OutsideConeVertex b => factor theta U v.val := by
    intro U
    rw [factor_outsideCone_representation theta b a U]
    change outsideConeFactor theta b a
      (spinMul (edgeNoise theta (U b)) (factor theta U b),
        fun w : OutsideConeNonroot b => U w.val) =
      outsideConeFactor theta b a
        (factor theta U (parent b), fun w : OutsideConeNonroot b => U w.val)
    have hspin : factor theta U b =
        spinMul (edgeNoise theta (U b)) (factor theta U (parent b)) := by
      change ofNoise (inputNoise theta U) b = _
      rw [ofNoise_nonroot _ b hb]
      simp only [inputNoise, ite_eq_right hb]
      rfl
    rw [hspin, spinMul_cancel]
  have hGrep : ∀ U : TreeVertex d → ℝ,
      G (factor theta U b, fun i : T => U i.val.val) =
        fun v : DescendantVertex b => factor theta U v.val := by
    intro U
    exact (factor_cone_representation theta b U).symm
  have h := condIndepFun_factor_disjoint_blocks theta b S T hST F G hF hG
  simpa only [hFrep, hGrep] using h

end Problem367.RootedBroadcast

end

end OAI
