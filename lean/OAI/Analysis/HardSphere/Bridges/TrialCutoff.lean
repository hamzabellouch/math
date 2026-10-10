import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeStrongRegular
import OAI.Analysis.HardSphere.Bridges.BridgeWindow

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_reverse (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    reverseConfigurationPath 1 L (projectCurve L (trialPath t y z u β))=
      projectCurve L (trialPath t z y u β.swap) := by
  have h₁ (s : Time) : leftTime (reverseTime s)=reverseTime (rightTime s) := by
    apply Subtype.ext
    change min (2*(1-(s:ℝ))) 1=1-max (2*(s:ℝ)-1) 0
    by_cases hs : (s:ℝ)≤1/2
    · rw [min_eq_right (by linarith),max_eq_right (by linarith)]; ring
    · rw [min_eq_left (by linarith),max_eq_left (by linarith)]; ring
  have h₂ (s : Time) : reverseTime (rightTime (reverseTime s))=leftTime s := by
    rw [←h₁,reverseTime_reverse]
  apply ContinuousMap.ext
  intro s
  change (fun _ j ↦ ((leg t y u (pinned β.1) (leftTime (reverseTime s))+leg t z u (pinned β.2) (reverseTime (rightTime (reverseTime s)))-u) j : AddCircle L.val))=_
  simp only [h₁,h₂,projectCurve,trialPath,ContinuousMap.coe_mk,Prod.fst_swap,Prod.snd_swap]
  ext i j
  congr 1
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

lemma trial_initial_diameter (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) (w : Time) :
    intervalDiameter 0 (prefixTime midpointTime w) (projectCurve L (trialPath t y z u β))=
      intervalDiameter 0 w (projectCurve L (leg t y u (pinned β.1))) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  have he (s : Time) : intervalTime 0 (prefixTime midpointTime w) s=prefixTime midpointTime (intervalTime 0 w s) := by
    apply Subtype.ext
    simp [intervalTime,prefixTime,midpointTime]
    ring
  change torusDistance L ((projectCurve L (trialPath t y z u β)) (intervalTime 0 (prefixTime midpointTime w) p.1) 0)
    ((projectCurve L (trialPath t y z u β)) (intervalTime 0 (prefixTime midpointTime w) p.2) 0)=_
  simp only [he,projectCurve,ContinuousMap.coe_mk,trial_left]
  rfl

lemma trial_endpoint_regular (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) (w : Time) {S : ℝ}
    (h₁ : liftedDiameter 0 w (pathCoordinates (leg t y u (pinned β.1)))≤S)
    (h₂ : liftedDiameter 0 w (pathCoordinates (leg t z u (pinned β.2)))≤S) :
    EndpointRegular (prefixTime midpointTime w) S (projectCurve L (trialPath t y z u β)) := by
  constructor
  · rw [trial_initial_diameter]
    exact (intervalDiameter_le_lifted (projectCurve_lift L _) 0 w).trans h₁
  · have h := trial_initial_diameter L t z y u β.swap w
    rw [←trial_reverse,intervalDiameter_reverse] at h
    simp only [reverseTime_zero,Prod.fst_swap] at h
    rw [h]
    exact (intervalDiameter_le_lifted (projectCurve_lift L _) 0 w).trans h₂

lemma prefix_or_suffix (s : Time) : (∃q : Time,prefixTime midpointTime q=s) ∨
    ∃q : Time,suffixTime midpointTime q=s := by
  by_cases hs : (s:ℝ)≤1/2
  · refine Or.inl ⟨⟨2*(s:ℝ),⟨by linarith [s.property.1],by linarith⟩⟩,?_⟩
    apply Subtype.ext
    change (1/2:ℝ)*(2*(s:ℝ))=(s:ℝ)
    ring
  · refine Or.inr ⟨⟨2*(s:ℝ)-1,⟨by linarith,by linarith [s.property.2]⟩⟩,?_⟩
    apply Subtype.ext
    change (1/2:ℝ)+(1-1/2)*(2*(s:ℝ)-1)=(s:ℝ)
    ring

def TrialConfined (L : Length) (v : Point) (f : C(Time,Point)) : Prop :=
  ∀s : Time,‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10

lemma trial_confined (L : Length) (t : ℝ) (y z u v : Point) (β : Noise×Noise)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (h₁ : incrementFluctuation t 1 0 1 (pinned β.1)≤1/3)
    (h₂ : incrementFluctuation t 1 0 1 (pinned β.2)≤1/3) :
    TrialConfined L v (trialPath t y z u β) := by
  intro s
  rcases prefix_or_suffix s with ⟨q,rfl⟩|⟨q,rfl⟩
  · rw [trial_left]
    exact leg_confined_of_fluctuation L t y u v (pinned β.1) hy hu (fun _ ↦ center_zero _) h₁ q
  · rw [trial_right]
    exact leg_confined_of_fluctuation L t z u v (pinned β.2) hz hu (fun _ ↦ center_zero _) h₂ (reverseTime q)

lemma trialConfined_measurable (L : Length) (v : Point) : MeasurableSet {f | TrialConfined L v f} := by
  have he : {f | TrialConfined L v f}=⋂s : Time,{f : C(Time,Point) | ‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10} := by ext f; simp [TrialConfined]
  rw [he]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro s
  change IsClosed ({f : C(Time,Point) | ‖f s-v‖≤10} ∩ {f | torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10})
  apply IsClosed.inter
  · exact isClosed_le ((continuous_eval_const s).sub continuous_const).norm continuous_const
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

def TrialCutoff (L : Length) (n : ℕ) (r R C : ℝ) (w : Time) (S : ℝ) (v : Point) (f : C(Time,Point)) : Prop :=
  Regular (n+n) r R C (prefixTime midpointTime w) S (projectCurve L f) ∧ TrialConfined L v f

lemma trialCutoff_measurable (L : Length) (n : ℕ) (r R C : ℝ) (w : Time) (S : ℝ) (v : Point) :
    MeasurableSet {f | TrialCutoff L n r R C w S v f} :=
  ((regular_measurable (n+n) r R C (prefixTime midpointTime w) S).preimage (projectCurve_continuous L).measurable).inter (trialConfined_measurable L v)

lemma trial_cutoff_of_legs (L : Length) {n : ℕ} {t r R C S : ℝ} (hr : 0<r)
    (y z u v : Point) (β : Noise×Noise) (w : Time)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (hm₁ : LegMeshRegular n t r R C y u (pinned β.1))
    (hm₂ : LegMeshRegular n t r R C z u (pinned β.2))
    (hw₁ : liftedDiameter 0 w (pathCoordinates (leg t y u (pinned β.1)))≤S)
    (hw₂ : liftedDiameter 0 w (pathCoordinates (leg t z u (pinned β.2)))≤S)
    (hc₁ : incrementFluctuation t 1 0 1 (pinned β.1)≤1/3)
    (hc₂ : incrementFluctuation t 1 0 1 (pinned β.2)≤1/3) :
    TrialCutoff L n r R C w S v (trialPath t y z u β) :=
  ⟨⟨trial_mesh_regular L hr y z u β hm₁ hm₂,trial_endpoint_regular L t y z u β w hw₁ hw₂⟩,
    trial_confined L t y z u v β hy hz hu hc₁ hc₂⟩

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma mesh_interval_time {n : ℕ} (j : Fin n) (q : Time) :
    intervalTime (meshTime j 0) (meshTime j 1) q=meshTime j q := by
  apply Subtype.ext
  dsimp [intervalTime,meshTime]
  ring

lemma prefix_representation (w q : Time) (hw : 0<(w:ℝ)) (hq : (q:ℝ)≤(w:ℝ)) :
    ∃u : Time,prefixTime w u=q := by
  refine ⟨⟨(q:ℝ)/(w:ℝ),⟨div_nonneg q.property.1 hw.le,(div_le_one hw).mpr hq⟩⟩,?_⟩
  apply Subtype.ext
  change (w:ℝ)*((q:ℝ)/(w:ℝ))=(q:ℝ)
  exact mul_div_cancel₀ _ hw.ne'

def meshLocalLift {L : Length} {n : ℕ} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (v : Point) (j : Fin n) : C(Time,Point) :=
  ⟨fun q k ↦ ζ k (suffixTime (meshTime j 0) q)-ζ k (meshTime j 0)+nearestLift L v (ω (meshTime j 0) 0) k,
    continuous_pi fun k ↦ (((ζ k).continuous.comp (suffixTime (meshTime j 0)).continuous).sub continuous_const).add continuous_const⟩

lemma meshLocalLift_zero {L : Length} {n : ℕ} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (v : Point) (j : Fin n) : meshLocalLift ω ζ v j 0=nearestLift L v (ω (meshTime j 0) 0) := by
  ext k
  simp [meshLocalLift,suffixTime_zero]

lemma meshLocalLift_project {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v : Point) (j : Fin n) (q : Time) :
    projectPoint L (meshLocalLift ω ζ v j q)=ω (suffixTime (meshTime j 0) q) 0 := by
  ext k
  change ((ζ k _-ζ k _+nearestLift L v _ k : ℝ) : AddCircle L.val)=_
  rw [AddCircle.coe_add,AddCircle.coe_sub,hζ,hζ]
  have hh := congrFun (nearestLift_project L v (ω (meshTime j 0) 0)) k
  change ((nearestLift L v (ω (meshTime j 0) 0) k:ℝ):AddCircle L.val)=_ at hh
  rw [hh,sub_add_cancel]

lemma meshLocalLift_increment {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v : Point) (j : Fin n) {δ : ℝ}
    (hδ : δ< L.val/2) (hd : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤δ)
    (q : Time) (hq : (q:ℝ)≤(meshRemainder j:ℝ)) :
    ‖meshLocalLift ω ζ v j q-meshLocalLift ω ζ v j 0‖≤δ := by
  obtain ⟨u,rfl⟩ := prefix_representation _ q (meshRemainder_pos j) hq
  have hd0 : 0≤δ := (intervalDiameter_nonneg _ _ _).trans hd
  apply (pi_norm_le_iff_of_nonneg hd0).mpr
  intro k
  change |(_- _ + _)-(_- _ + _)|≤δ
  simp only [suffixTime_zero,mesh_suffix_time,sub_self,zero_add,add_sub_cancel_right]
  have hh := liftDiff_norm_eq hζ (meshTime j 0) (meshTime j 1) (hd.trans_lt hδ) k u 0
  simp only [mesh_interval_time] at hh
  rw [←hh]
  have hi : torusDistance L (ω (meshTime j u) 0) (ω (meshTime j 0) 0)≤δ := by
    have h := intervalDistance_le (meshTime j 0) (meshTime j 1) u 0 ω
    simp only [mesh_interval_time] at h
    exact h.trans hd
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ k).trans hi

lemma mesh_torus_hit_local {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v x : Point) (j : Fin n) (q : Time) {δ r : ℝ}
    (hL : 50< L.val) (hδ : δ≤1) (hd : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤δ)
    (hx : ‖x-v‖≤10) (hxT : torusDistance L (projectPoint L x) (projectPoint L v)≤10)
    (hr : r≤1) (hit : torusDistance L (projectPoint L x) (ω (meshTime j q) 0)≤ r) :
    torusDistance L (ω (meshTime j 0) 0) (projectPoint L v)≤12 ∧
    ‖x-meshLocalLift ω ζ v j (prefixTime (meshRemainder j) q)‖≤ r := by
  have hos : torusDistance L (ω (meshTime j 0) 0) (ω (meshTime j q) 0)≤δ := by
    have h := intervalDistance_le (meshTime j 0) (meshTime j 1) 0 q ω
    simp only [mesh_interval_time] at h
    exact h.trans hd
  have hn : torusDistance L (ω (meshTime j 0) 0) (projectPoint L v)≤12 := by
    have h1 := torusDistance_triangle' L (ω (meshTime j 0) 0) (ω (meshTime j q) 0) (projectPoint L v)
    have h2 := torusDistance_triangle' L (ω (meshTime j q) 0) (projectPoint L x) (projectPoint L v)
    rw [torusDistance_comm L (ω (meshTime j q) 0) (projectPoint L x)] at h2
    linarith
  refine ⟨hn,?_⟩
  have hc := meshLocalLift_increment hζ v j (show δ< L.val/2 by linarith) hd (prefixTime (meshRemainder j) q)
    (show (prefixTime (meshRemainder j) q:ℝ)≤(meshRemainder j:ℝ) by
      change (meshRemainder j:ℝ)*(q:ℝ)≤(meshRemainder j:ℝ)
      nlinarith [q.property.2,(meshRemainder j).property.1])
  apply local_collision_lifts hL hx (c₀:=meshLocalLift ω ζ v j 0)
    (by rw [meshLocalLift_zero]; exact nearestLift_bound L v _ hn) (hc.trans hδ)
  simpa only [meshLocalLift_project hζ,mesh_suffix_time] using hit

end HardSphere.Bridge

end
end

end

end OAI
