import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeAverage

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def LegMeshRegular (n : ℕ) (t r R C : ℝ) (y u : Point) (β : Noise) : Prop :=
  (∀j : Fin n,legMeshRatio t r y u j β≤R) ∧
   (∑j : Fin n,legCost t r y u j β)≤C*(n:ℝ)

lemma legMeshRegular_measurable (n : ℕ) (t r R C : ℝ) (y u : Point) :
    MeasurableSet {β | LegMeshRegular n t r R C y u β} := by
  have he : {β | LegMeshRegular n t r R C y u β} = ((⋂j : Fin n,{β | legMeshRatio t r y u j β≤R}) ∩
    {β | (∑j : Fin n,legCost t r y u j β)≤C*(n:ℝ)}) := by ext β; simp [LegMeshRegular]
  rw [he]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    unfold legMeshRatio
    have hζ : Continuous (fun β : Noise ↦ fun i : Fin 3 ↦
        (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩) := by
      apply continuous_pi; intro i
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : Noise×Time ↦ leg t y u p.1 (meshTime j p.2) i)
      have hl := leg_continuous t y u
      have hj := meshTime_continuous j
      fun_prop
    exact (((liftedDiameter_continuous 0 1).comp hζ).div_const r).measurable
  · exact measurableSet_le (Finset.measurable_fun_sum _ (fun j _ ↦ (legCost_continuous j t r y u).measurable)) measurable_const

lemma strong_mesh_of_free (L : Length) (n : ℕ) {t r R B C Creg : ℝ} (hr : 0<r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ)≤r) (hsmall : R*r<L.val/2)
    (hfree : MeshRegular n r R Creg (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))) :
    LegMeshRegular n t r (3*(1+R)) (64*Creg) y u (centeredNoise w) := by
  have he (j : Fin n) := mesh_lift_diameter (rawPath_lift L t y w) hr hsmall hfree.1 j
  have hd (j : Fin n) : legMeshRatio t r y u j (centeredNoise w)≤
      3*(1+diameterRatio r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) := by
    have h := centered_leg_mesh_diameter j hr y u w hdis hw hdrift
    rw [he j] at h
    exact h
  constructor
  · intro j
    exact (hd j).trans (by linarith [hfree.1 j])
  · calc
      _ ≤ ∑j : Fin n,64*cubicCost r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))) := by
        apply Finset.sum_le_sum
        intro j _
        have hnon : 0≤legMeshRatio t r y u j (centeredNoise w) := div_nonneg (norm_nonneg _) hr.le
        have h := pow_le_pow_left₀ (by linarith : 0≤1+legMeshRatio t r y u j (centeredNoise w))
          (show 1+legMeshRatio t r y u j (centeredNoise w)≤4*(1+diameterRatio r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) by
            have hn := diameterRatio_nonneg hr.le (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))
            linarith [hd j]) 3
        simpa only [mul_pow,show (4:ℝ)^3=64 by norm_num,legCost,cubicCost,legMeshRatio] using h
      _ = 64*(∑j : Fin n,cubicCost r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) := (Finset.mul_sum ..).symm
      _ ≤ 64*(Creg*(n:ℝ)) := mul_le_mul_of_nonneg_left hfree.2 (by norm_num)
      _ = _ := by ring

lemma raw_norm_tail {c B : ℝ} {M : ℝ≥0∞} (hB : 0≤B)
    (htail : ∀R : ℝ,0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2))) :
    coordinateWiener 1 {w | ¬∀i : Fin 3,‖w (0,i)‖≤B}≤3*(M*ENNReal.ofReal (Real.exp (-c*B^2))) := by
  have he : {w : CoordinatePaths 1 | ¬∀i : Fin 3,‖w (0,i)‖≤B} = ⋃i : Fin 3,{w | B<‖w (0,i)‖} := by ext w; simp
  rw [he]
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    _ ≤ ∑_i : Fin 3,M*ENNReal.ofReal (Real.exp (-c*B^2)) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,i)
      have hset : MeasurableSet {f : C(Time,ℝ) | B<‖f‖} := measurableSet_lt measurable_const (by fun_prop)
      change (Measure.pi fun _ : Direction 1 ↦ wiener) ((Function.eval (0,i)) ⁻¹' {f : C(Time,ℝ) | B<‖f‖})≤_
      rw [hm.measure_preimage hset.nullMeasurableSet]
      exact (measure_mono (show {f : C(Time,ℝ) | B<‖f‖}⊆{f | B≤‖f‖} from by intro f hf; change B<‖f‖ at hf; change B≤‖f‖; exact le_of_lt hf)).trans (htail B hB)
    _ = _ := by simp [nsmul_eq_mul]

lemma strong_leg_mesh_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ,0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0<n) {t r R B C : ℝ}
    (ht : 0<t) (hr : 0<r) (hτr : t/(n:ℝ)≤r^2) (hR : 0≤R) (hB : 0≤B)
    (y u : Point) (hdis : ‖u-y‖≤C)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ)≤r) (hsmall : R*r<L.val/2) :
    law {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β}≤
      (n:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
        ENNReal.ofReal (Real.exp (-(n:ℝ)/((1+R)^3)))+
        3*(M*ENNReal.ofReal (Real.exp (-c*B^2))) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have he : MeasurableSet {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β} := (legMeshRegular_measurable n t r (3*(1+R)) (64*(meanCost+1)) y u).compl
  rw [←centeredNoise_preserving.measure_preimage he.nullMeasurableSet]
  have hsub : centeredNoise ⁻¹' {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β} ⊆
      {w | ¬MeshRegular n r R (meanCost+1) (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))} ∪
      {w | ¬∀i : Fin 3,‖w (0,i)‖≤B} := by
    intro w hw
    by_contra hn
    have hh := not_or.mp hn
    exact hw (strong_mesh_of_free L n hr y u w hdis (not_not.mp hh.2) hdrift hsmall (not_not.mp hh.1))
  have hfree := free_mesh_regular_tail htail hr (div_pos ht hn') hτr hR n hn (fun _ j ↦ (y j:AddCircle L.val))
  rw [mul_div_cancel₀ _ (ne_of_gt hn')] at hfree
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans (add_le_add hfree (raw_norm_tail hB htail))

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def projectCurve (L : Length) (f : C(Time,Point)) : ConfigurationPath 1 L :=
  ⟨fun s _ j ↦ (f s j:AddCircle L.val),by fun_prop⟩
lemma projectCurve_lift (L : Length) (f : C(Time,Point)) : IsPathLift (projectCurve L f) (pathCoordinates f) := by
  intro j s
  rfl
lemma projectCurve_continuous (L : Length) : Continuous (projectCurve L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(Time,Point)×Time ↦ fun _ : Fin 1 ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
  fun_prop

lemma trial_left (t : ℝ) (y z u : Point) (β : Noise×Noise) (s : Time) :
    trialPath t y z u β (prefixTime midpointTime s)=leg t y u (pinned β.1) s := by
  have hl : leftTime (prefixTime midpointTime s)=s := by
    apply Subtype.ext
    change min (2*((1/2:ℝ)*(s:ℝ))) 1=(s:ℝ)
    rw [show 2*((1/2:ℝ)*(s:ℝ))=(s:ℝ) by ring,min_eq_left s.property.2]
  have hr : reverseTime (rightTime (prefixTime midpointTime s))=1 := by
    apply Subtype.ext
    change 1-max (2*((1/2:ℝ)*(s:ℝ))-1) 0=1
    rw [max_eq_right (by linarith [s.property.2])]
    ring
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one,add_sub_cancel_right]

lemma trial_right (t : ℝ) (y z u : Point) (β : Noise×Noise) (s : Time) :
    trialPath t y z u β (suffixTime midpointTime s)=leg t z u (pinned β.2) (reverseTime s) := by
  have hl : leftTime (suffixTime midpointTime s)=1 := by
    apply Subtype.ext
    change min (2*((1/2:ℝ)+(1-1/2)*(s:ℝ))) 1=1
    rw [min_eq_right (by linarith [s.property.1])]
  have hr : rightTime (suffixTime midpointTime s)=s := by
    apply Subtype.ext
    change max (2*((1/2:ℝ)+(1-1/2)*(s:ℝ))-1) 0=(s:ℝ)
    rw [show 2*((1/2:ℝ)+(1-1/2)*(s:ℝ))-1=(s:ℝ) by ring,max_eq_left s.property.1]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one]
  abel

lemma mesh_first_half {n : ℕ} (j : Fin n) (s : Time) :
    meshTime (j.castAdd n) s=prefixTime midpointTime (meshTime j s) := by
  apply Subtype.ext
  simp only [meshTime,Fin.val_castAdd,Nat.cast_add,prefixTime,midpointTime,ContinuousMap.coe_mk]
  ring
lemma mesh_second_half {n : ℕ} (j : Fin n) (s : Time) :
    meshTime (j.natAdd n) s=suffixTime midpointTime (meshTime j s) := by
  apply Subtype.ext
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  simp only [meshTime,Fin.val_natAdd,Nat.cast_add,suffixTime,midpointTime,ContinuousMap.coe_mk]
  field_simp [hn]
  ring

lemma trial_mesh_left (L : Length) {n : ℕ} (j : Fin n) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    meshSegment (j.castAdd n) (projectCurve L (trialPath t y z u β))=
      meshSegment j (projectCurve L (leg t y u (pinned β.1))) := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,ContinuousMap.coe_mk,projectCurve,mesh_first_half,trial_left]

lemma trial_mesh_right (L : Length) {n : ℕ} (j : Fin n) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    meshSegment (j.natAdd n) (projectCurve L (trialPath t y z u β))=
      meshSegment j (reverseConfigurationPath 1 L (projectCurve L (leg t z u (pinned β.2)))) := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,ContinuousMap.coe_mk,projectCurve,mesh_second_half,trial_right]
  rfl

lemma project_leg_mesh_regular (L : Length) {n : ℕ} {t r R C : ℝ} (hr : 0<r)
    (y u : Point) (β : Noise) (h : LegMeshRegular n t r R C y u β) :
    MeshRegular n r R C (projectCurve L (leg t y u β)) := by
  have hd (j : Fin n) : diameterRatio r (meshSegment j (projectCurve L (leg t y u β)))≤legMeshRatio t r y u j β :=
    div_le_div_of_nonneg_right (intervalDiameter_le_lifted (meshSegment_lift (projectCurve_lift L (leg t y u β)) j) 0 1) hr.le
  constructor
  · intro j
    exact (hd j).trans (h.1 j)
  · apply le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) h.2
    change (1+diameterRatio r (meshSegment j (projectCurve L (leg t y u β))))^3 ≤ (1+legMeshRatio t r y u j β)^3
    exact pow_le_pow_left₀ (by linarith [diameterRatio_nonneg hr.le (meshSegment j (projectCurve L (leg t y u β)))]) (by linarith [hd j]) 3

lemma trial_mesh_regular (L : Length) {n : ℕ} {t r R C : ℝ} (hr : 0<r)
    (y z u : Point) (β : Noise×Noise)
    (h₁ : LegMeshRegular n t r R C y u (pinned β.1))
    (h₂ : LegMeshRegular n t r R C z u (pinned β.2)) :
    MeshRegular (n+n) r R C (projectCurve L (trialPath t y z u β)) := by
  have hl := project_leg_mesh_regular L hr y u (pinned β.1) h₁
  have hrr := project_leg_mesh_regular L hr z u (pinned β.2) h₂
  have hright := (meshRegular_reverse (L:=L) n r R C _).mpr hrr
  constructor
  · refine (Fin.forall_fin_add (fun j : Fin (n+n) ↦ diameterRatio r (meshSegment j (projectCurve L (trialPath t y z u β)))≤R)).mpr ?_
    constructor
    · intro j
      rw [trial_mesh_left]
      exact hl.1 j
    · intro j
      rw [trial_mesh_right]
      exact hright.1 j
  · rw [Fin.sum_univ_add]
    simp_rw [trial_mesh_left,trial_mesh_right]
    have h := add_le_add hl.2 hright.2
    simpa only [Nat.cast_add,mul_add] using h

end HardSphere.Bridge

end
end

end

end OAI
