import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalInsertionBound
import OAI.Analysis.HardSphere.Bridges.PhysicalInsertion

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking
attribute [local irreducible] torusDistance

lemma intervalTime_full (s : Time) : intervalTime 0 1 s=s := by
  apply Subtype.ext
  simp [intervalTime]

lemma tube_diameter {L : Length} (ω : ConfigurationPath 1 L) (c : Torus L)
    (hc : ∀s : Time,torusDistance L (ω s 0) c≤10) : intervalDiameter 0 1 ω≤20 := by
  apply intervalDiameter_le _ _ _ (by norm_num)
  intro s q
  simp only [intervalTime_full]
  have htri := torusDistance_triangle' L (ω s 0) c (ω q 0)
  rw [torusDistance_comm L c] at htri
  linarith [hc s,hc q]

lemma lift_norm_increment {L : Length} (hL : 50<L.val) (f : C(Time,Point))
    (hd : intervalDiameter 0 1 (projectCurve L f)≤20) (s : Time) :
    ‖f s-f 0‖≤20 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤20)).mpr
  intro j
  have he := liftDiff_norm_eq (projectCurve_lift L f) 0 1 (hd.trans_lt (by linarith)) j s 0
  simp only [intervalTime_full] at he
  change dist (projectPoint L (f s) j) (projectPoint L (f 0) j)=|f s j-f 0 j| at he
  change |f s j-f 0 j|≤20
  rw [←he]
  have hd' := intervalDistance_le 0 1 s 0 (projectCurve L f)
  simp only [intervalTime_full] at hd'
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans (hd'.trans hd)

lemma scalar_dist_eq {L : Length} (x y : ℝ) (h : |x-y|≤L.val/2) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)=|x-y| := by
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr
    (show |x-y|≤|L.val|/2 by simpa only [abs_of_pos L.property] using h)
  simpa only [AddCircle.coe_sub,dist_eq_norm] using he

lemma local_norm_le_torus {L : Length} (hL : 50<L.val) (x v : Point)
    (hx : ‖x-v‖≤23) : ‖x-v‖≤torusDistance L (projectPoint L x) (projectPoint L v) := by
  apply (pi_norm_le_iff_of_nonneg (torusDistance_nonnegative _ _ _)).mpr
  intro j
  have hb : ‖(x-v) j‖≤23 := (norm_le_pi_norm (x-v) j).trans hx
  have hbound : |x j-v j|≤23 := hb
  have he : dist (projectPoint L x j) (projectPoint L v j)=|x j-v j| :=
    scalar_dist_eq (x j) (v j) (by linarith)
  change |x j-v j|≤_
  rw [←he]
  exact CellOrbital.dist_coord_le_torusDistance L _ _ j

lemma confined_lift {L : Length} (hL : 50<L.val) (v : Point) (f : C(Time,Point))
    (h0 : ‖f 0-v‖≤3)
    (hc : ∀s : Time,torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10) :
    TrialConfined L v f := by
  have hd := tube_diameter (projectCurve L f) (projectPoint L v) hc
  intro s
  refine ⟨?_,hc s⟩
  have hin := lift_norm_increment hL f hd s
  have h23 : ‖f s-v‖≤23 := by
    have htri := norm_sub_le (f s - f 0) (v - f 0)
    have he : f s-v = (f s-f 0)-(v-f 0) := by abel
    have hev : ‖v-f 0‖=‖f 0-v‖ := norm_sub_rev _ _
    rw [←he,hev] at htri
    linarith
  exact (local_norm_le_torus hL (f s) v h23).trans (hc s)

lemma leg_translate (t : ℝ) (y z c : Point) (β : Noise) :
    leg t (y+c) (z+c) β=leg t y z β+ContinuousMap.const _ c := by
  ext s j
  change (1-(s:ℝ))*(y j+c j)+(s:ℝ)*(z j+c j)+Real.sqrt (2*t)*β j s=
    ((1-(s:ℝ))*y j+(s:ℝ)*z j+Real.sqrt (2*t)*β j s)+c j
  ring

lemma project_leg_shift {L : Length} (t : ℝ) (y z c : Point) (β : Noise)
    (hc : projectPoint L c=0) :
    projectCurve L (leg t (y+c) (z+c) β)=projectCurve L (leg t y z β) := by
  rw [leg_translate]
  ext s i j
  change (((leg t y z β s j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]
  rfl

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def permittedPath {J : Type*} {L : Length} (n : ℕ) (r R Creg S : ℝ)
    (w : Time) (y z v : Point) (F : J → ConfigurationPath 1 L) : Set C(Time,Point) :=
  {f | Regular n r R Creg w S (projectCurve L f) ∧ TrialConfined L v f ∧
    f∈fixedEndpoints y z ∧ ∀j,¬TrialCollision r (F j) f}

lemma permittedPath_measurable {J : Type*} [Countable J] {L : Length}
    (n : ℕ) (r R Creg S : ℝ) (w : Time) (y z v : Point) (F : J → ConfigurationPath 1 L) :
    MeasurableSet (permittedPath n r R Creg S w y z v F) := by
  apply ((regular_measurable n r R Creg w S).preimage (projectCurve_continuous L).measurable).inter
  apply (trialConfined_measurable L v).inter
  apply (fixedEndpoints_measurable y z).inter
  change MeasurableSet {f : C(Time,Point) | ∀j,¬TrialCollision r (F j) f}
  have he : {f : C(Time,Point) | ∀j,¬TrialCollision r (F j) f}=⋂j,{f | ¬TrialCollision r (F j) f} := by
    ext f
    simp only [mem_ofPred_eq,mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j ↦ (trialCollision_closed r (F j)).measurableSet.compl)

lemma permitted_reference_collision {J J' : Type*} [Countable J] [Countable J']
    {L : Length} {n : ℕ} (hn : 0<n)
    (y z v y' z' v' : Point) (F : J → ConfigurationPath 1 L) (F' : J' → ConfigurationPath 1 L)
    (w : Time) {t r S h R Creg C : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hR : 0≤R)
    (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/(2*t))
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3)
    (hsmall : r*R≤1) (hτr : (2*t)/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(n:ℝ))≤h) (hlarge : 8*(2*t)≤(n:ℝ)*h) (hdrift : 26/(n:ℝ)≤r)
    (hsep0 : r+2*S<torusDistance L (projectPoint L y) (projectPoint L y'))
    (hsep1 : r+2*S<torusDistance L (projectPoint L z) (projectPoint L z'))
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hC : 0≤C) (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    {c : ℝ≥0∞} (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u (permittedPath n r R Creg S w y z v F))
    (g : permittedPath n r R Creg S w y' z' v' F') :
    referenceOn t y z (permittedPath n r R Creg S w y z v F)
      {f | TrialCollision r (projectCurve L g.val) f.val}≤
      (c*(volume A*midpointLower t C))⁻¹*
      (2*ENNReal.ofReal (hitConstant*(4*Creg*(2*t)*r+8*r*(1+R)^3/Real.sqrt (h/2)))) := by
  rw [referenceOn_collision t r y z (permittedPath_measurable ..)]
  apply individual_collision_bound hn y z v (projectCurve L g.val) w hL ht hr hr1 hR hCreg hh hw hy hz
    g.property.1 hsmall hτr hnscale hwindow hlarge hdrift _ _ hA hA0 hAfinite hC hbound
    (permittedPath n r R Creg S w y z v F) (permittedPath_measurable ..) _ hc
  · simpa only [projectCurve,ContinuousMap.coe_mk,g.property.2.2.1.1] using hsep0
  · simpa only [projectCurve,ContinuousMap.coe_mk,g.property.2.2.1.2] using hsep1
  · intro f hf
    exact ⟨hf.1,hf.2.1⟩

lemma near_end_of_confined_leg {L : Length} (hL : 50<L.val) (t : ℝ)
    (y z v : Point) (β : Noise) (hy : ‖y-v‖≤3)
    (hβ : leg t y z β 0=y ∧ leg t y z β 1=z)
    (hc : ∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10)
    (hz : torusDistance L (projectPoint L z) (projectPoint L v)≤3) : ‖z-v‖≤3 := by
  have htube := confined_lift hL v (leg t y z β) (by simpa only [hβ.1] using hy) hc
  have h10 : ‖z-v‖≤10 := by simpa only [hβ.2] using (htube 1).1
  exact (local_norm_le_torus hL z v (h10.trans (by norm_num))).trans hz

lemma near_end_of_positive_confined {L : Length} (hL : 50<L.val) (t : ℝ)
    (y z v : Point) (hy : ‖y-v‖≤3)
    (hz : torusDistance L (projectPoint L z) (projectPoint L v)≤3)
    (hp : law {β | ∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10}≠0) :
    ‖z-v‖≤3 := by
  by_contra h
  apply hp
  have hh : ∀ᵐβ ∂law,¬(∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10) := by
    filter_upwards [leg_endpoints_ae t y z] with β hβ hc
    exact h (near_end_of_confined_leg hL t y z v β hy hβ hc hz)
  simpa only [not_not] using ae_iff.mp hh

end HardSphere.Bridge

end
end

end

end OAI
