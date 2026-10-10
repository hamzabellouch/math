import OAI.Probability.FreeIsing.Posterior.LatentObservationIndependence
import OAI.Probability.FreeIsing.Trees.BroadcastBranchLabels
import OAI.Probability.FreeIsing.Trees.BroadcastJointLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem map_factor_disjoint_blocks {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (S T : Set (NonrootVertex d)) (hST : Disjoint S T) :
    (labelMeasure d).map (fun U => (factor theta U v,
      (fun i : S => U i.val.val), (fun i : T => U i.val.val))) =
      (uniform01.map fairSpin).prod
        ((Measure.infinitePi (fun _ : S => uniform01)).prod
          (Measure.infinitePi (fun _ : T => uniform01))) := by
  let H : (NonrootVertex d → ℝ) → (S → ℝ) × (T → ℝ) :=
    fun Y => ((fun i => Y i.val), (fun i => Y i.val))
  have hH : Measurable H := by fun_prop
  have hJ : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U v, fun w : NonrootVertex d => U w.val)) :=
    ((measurable_pi_apply v).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val))
  have hmap : (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)).map H =
      (Measure.infinitePi (fun _ : S => uniform01)).prod
        (Measure.infinitePi (fun _ : T => uniform01)) :=
    map_disjoint_subarrays (fun _ : NonrootVertex d => uniform01) S T hST
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U v, fun w : NonrootVertex d => U w.val))).map (Prod.map id H) := by
      rw [Measure.map_map (measurable_id.prodMap hH) hJ]
      rfl
    _ = _ := by
      rw [map_factor_rest]
      rw [← Measure.map_prod_map _ _ measurable_id hH]
      rw [Measure.map_id, hmap]

theorem condIndepFun_factor_disjoint_blocks {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (S T : Set (NonrootVertex d)) (hST : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin × (S → ℝ) → A) (G : IsingSpin × (T → ℝ) → B)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (MeasurableSpace.comap (fun U => factor theta U v) inferInstance)
      (((measurable_pi_apply v).comp (measurable_factor d theta)).comap_le)
      (fun U => F (factor theta U v, fun i : S => U i.val.val))
      (fun U => G (factor theta U v, fun i : T => U i.val.val))
      (labelMeasure d) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  exact condIndepFun_of_product_jointLaw (labelMeasure d) (uniform01.map fairSpin)
    (Measure.infinitePi (fun _ : S => uniform01))
    (Measure.infinitePi (fun _ : T => uniform01))
    ((measurable_pi_apply v).comp (measurable_factor d theta))
    (by fun_prop) (by fun_prop) (map_factor_disjoint_blocks theta v S T hST)
    F G hF hG

end Problem367.RootedBroadcast

end

end OAI
