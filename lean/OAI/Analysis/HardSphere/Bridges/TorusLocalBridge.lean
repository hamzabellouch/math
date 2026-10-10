import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhaseBridge

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def localLiftChart {N : ℕ} (L : Length) (c : LiftedConfiguration N) : Set (LiftedConfiguration N) :=
  univ.pi (fun i ↦ univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))

lemma localLiftChart_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    MeasurePreserving (project N L) (volume.restrict (localLiftChart L c)) volume := by
  have hi (i : Fin N) : MeasurePreserving (fun x : Fin 3 → ℝ ↦ fun j ↦ (x j : AddCircle L.val))
      (volume.restrict (univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))) volume := by
    have hp := measurePreserving_pi (fun j : Fin 3 ↦ volume.restrict (Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
      (f:=fun _ x ↦ (x:AddCircle L.val)) (fun j ↦ AddCircle.measurePreserving_mk L.val (c i j-L.val/2))
    change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _) (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
    simpa only [Measure.restrict_pi_pi] using hp
  have hp := measurePreserving_pi
    (fun i ↦ volume.restrict (univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val))))
    (fun _ : Fin N ↦ (volume : Measure (Torus L))) hi
  change MeasurePreserving (fun X : LiftedConfiguration N ↦ fun i j ↦ (X i j : AddCircle L.val)) ((Measure.pi (fun _ : Fin N ↦ (volume : Measure (Fin 3 → ℝ)))).restrict _) (Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))))
  simpa only [project,localLiftChart,Measure.restrict_pi_pi] using hp

lemma project_injOn_chart {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    Set.InjOn (project N L) (localLiftChart L c) := by
  intro X hX Y hY he
  funext i j
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hX i (mem_univ i) j (mem_univ j))
    (hY i (mem_univ i) j (mem_univ j))).mp (congrFun (congrFun he i) j)

lemma ball_subset_localLiftChart {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : Metric.ball c r ⊆ localLiftChart L c := by
  intro X hX i hi j hj
  have hd : dist (X i j) (c i j)<r :=
    (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hX)
  rw [Real.dist_eq,abs_lt] at hd
  constructor <;> linarith

lemma isOpenMap_project (N : ℕ) (L : Length) : IsOpenMap (project N L) := by
  have hcircle : Function.Surjective (fun t : ℝ ↦ (t : AddCircle L.val)) := by
    intro x
    exact ⟨(AddCircle.equivIco L.val 0 x).val,AddCircle.coe_equivIco⟩
  have hopen : IsOpenMap (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe) (Eventually.of_forall (fun _ ↦ hcircle))
  exact IsOpenMap.piMap (fun _ : Fin N ↦ hopen)
    (Eventually.of_forall (fun _ ↦ Function.Surjective.piMap (fun _ ↦ hcircle)))

lemma project_ball_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : MeasurePreserving (project N L) (volume.restrict (Metric.ball c r))
      (volume.restrict ((project N L) '' Metric.ball c r)) := by
  have hsub := ball_subset_localLiftChart L c hr
  have he : (project N L) ⁻¹' ((project N L) '' Metric.ball c r) ∩ localLiftChart L c=Metric.ball c r := by
    ext X
    constructor
    · rintro ⟨⟨Y,hY,hYX⟩,hX⟩
      exact (project_injOn_chart L c (hsub hY) hX hYX) ▸ hY
    · intro hX
      exact ⟨mem_image_of_mem _ hX,hsub hX⟩
  have h := (localLiftChart_preserving L c).restrict_preimage
    ((isOpenMap_project N L) (Metric.ball c r) Metric.isOpen_ball).measurableSet
  rw [Measure.restrict_restrict (((isOpenMap_project N L) (Metric.ball c r) Metric.isOpen_ball).measurableSet.preimage (continuous_project N L).measurable),he] at h
  exact h

lemma killed_ae_torus_local_pairs {N : ℕ} (L : Length) (a : ℝ)
    {P : Configuration N L → Configuration N L → Prop}
    (hPm : MeasurableSet {p : Configuration N L×Configuration N L | P p.1 p.2})
    (hP : ∀t, 0<t → ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1))
    {x : Configuration N L} (hx : x∈allowed N L a) :
    ∃ U : Set (Configuration N L), IsOpen U ∧ x∈U ∧ U⊆allowed N L a ∧
      ∀ᵐ X ∂volume.restrict U, ∀ᵐ Y ∂volume.restrict U, P X Y := by
  let c := representative N L x
  have hc : c∈(project N L) ⁻¹' allowed N L a := by simpa [c] using hx
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp ((isOpen_allowed N L a).preimage (continuous_project N L)) c hc
  let S := min R L.val
  have hS : 0<S := lt_min hR L.property
  have hb : Metric.ball c S ⊆ (project N L) ⁻¹' allowed N L a :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  let U := (project N L) '' Metric.ball c (S/2)
  have hU : IsOpen U := (isOpenMap_project N L) _ Metric.isOpen_ball
  refine ⟨U,hU,?_,?_,?_⟩
  · exact ⟨c,Metric.mem_ball_self (by positivity),project_representative N L x⟩
  · rintro _ ⟨X,hX,rfl⟩
    exact hb ((Metric.ball_subset_ball (by linarith : S/2≤S)) hX)
  · have h := killed_ae_local_pairs L a hP c hS (min_le_right _ _) hb
    have hp := project_ball_preserving L c (show S/2≤L.val/2 from div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    have hh : ∀ᵐ p ∂(volume.restrict U).prod (volume.restrict U), P p.1 p.2 := by
      rw [←(hp.prod hp).map_eq,ae_map_iff (hp.prod hp).measurable.aemeasurable hPm]
      exact (ae_prod_iff_ae_ae (hPm.preimage (hp.prod hp).measurable)).mpr h
    exact ae_ae_of_ae_prod hh

end HardSphere

end
end

end

end OAI
