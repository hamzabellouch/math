import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReverseConfigurationPath
import OAI.Analysis.HardSphere.Bridges.NormalizedPrefix
import OAI.Analysis.HardSphere.Geometry.InjectiveNear

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def intervalTime (a b s : Time) : Time :=
  ⟨(1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) a.property.1) (mul_nonneg s.property.1 b.property.1)
    · nlinarith [a.property.1,a.property.2,b.property.1,b.property.2,
        s.property.1,s.property.2,mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr a.property.2),
        mul_nonneg s.property.1 (sub_nonneg.mpr b.property.2)]⟩

lemma intervalTime_continuous (a b : Time) : Continuous (intervalTime a b) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] lemma intervalTime_zero (a b : Time) : intervalTime a b 0=a := by
  apply Subtype.ext
  simp [intervalTime]
@[simp] lemma intervalTime_one (a b : Time) : intervalTime a b 1=b := by
  apply Subtype.ext
  simp [intervalTime]

def diameterMap {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) : C(Time×Time,ℝ) :=
  ⟨fun p ↦ torusDistance L (ω (intervalTime a b p.1) 0) (ω (intervalTime a b p.2) 0), by
    apply (torusDistance_continuous_pair L).comp (f := fun p : Time×Time ↦ (ω (intervalTime a b p.1) 0,ω (intervalTime a b p.2) 0))
    exact ((continuous_apply 0).comp (ω.continuous.comp ((intervalTime_continuous a b).comp continuous_fst))).prodMk
      ((continuous_apply 0).comp (ω.continuous.comp ((intervalTime_continuous a b).comp continuous_snd)))⟩

def intervalDiameter {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) : ℝ :=
  ‖diameterMap a b ω‖

lemma diameterMap_continuous (L : Length) (a b : Time) : Continuous (diameterMap (L:=L) a b) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath 1 L × (Time×Time) ↦
    torusDistance L (p.1 (intervalTime a b p.2.1) 0) (p.1 (intervalTime a b p.2.2) 0))
  apply (torusDistance_continuous_pair L).comp (f := fun p : ConfigurationPath 1 L×(Time×Time) ↦ (p.1 (intervalTime a b p.2.1) 0,p.1 (intervalTime a b p.2.2) 0))
  apply Continuous.prodMk
  · exact (continuous_apply 0).comp (continuous_fst.eval ((intervalTime_continuous a b).comp (continuous_fst.comp continuous_snd)))
  · exact (continuous_apply 0).comp (continuous_fst.eval ((intervalTime_continuous a b).comp (continuous_snd.comp continuous_snd)))

lemma intervalDiameter_continuous (L : Length) (a b : Time) :
    Continuous (intervalDiameter (L:=L) a b) := (diameterMap_continuous L a b).norm

lemma intervalDiameter_nonneg {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    0 ≤ intervalDiameter a b ω := norm_nonneg _

lemma intervalDistance_le {L : Length} (a b s q : Time) (ω : ConfigurationPath 1 L) :
    torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ intervalDiameter a b ω := by
  exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (diameterMap a b ω) (s,q))

lemma intervalDiameter_le {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s q, torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ R) :
    intervalDiameter a b ω ≤ R := by
  apply (ContinuousMap.norm_le _ hR).mpr
  intro p
  change |torusDistance L _ _| ≤ R
  rw [abs_of_nonneg (by unfold torusDistance; positivity)]
  exact h p.1 p.2

lemma intervalTime_reverse (a b s : Time) :
    reverseTime (intervalTime a b s)=intervalTime (reverseTime b) (reverseTime a) (reverseTime s) := by
  apply Subtype.ext
  change 1-((1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ)) = (1-(1-(s:ℝ)))*(1-(b:ℝ))+(1-(s:ℝ))*(1-(a:ℝ))
  ring

lemma intervalDiameter_reverse {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter a b (reverseConfigurationPath 1 L ω)=
      intervalDiameter (reverseTime b) (reverseTime a) ω := by
  apply le_antisymm
  · apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    change torusDistance L (ω (reverseTime (intervalTime a b s)) 0)
      (ω (reverseTime (intervalTime a b q)) 0) ≤ _
    simp only [intervalTime_reverse]
    exact intervalDistance_le _ _ _ _ _
  · have hh : reverseTime (reverseTime a)=a := reverseTime_reverse _
    have hh' : reverseTime (reverseTime b)=b := reverseTime_reverse _
    apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    have h := intervalDistance_le a b (reverseTime s) (reverseTime q) (reverseConfigurationPath 1 L ω)
    change torusDistance L (ω (reverseTime (intervalTime a b (reverseTime s))) 0)
      (ω (reverseTime (intervalTime a b (reverseTime q))) 0) ≤ _ at h
    simpa only [intervalTime_reverse,reverseTime_reverse] using h

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshTime {m : ℕ} (j : Fin m) (s : Time) : Time :=
  ⟨((j:ℝ)+(s:ℝ))/(m:ℝ), by
    have hm : (0:ℝ) < m := by exact_mod_cast j.pos
    refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) s.property.1) hm.le,(div_le_one hm).mpr ?_⟩
    have hj : (j:ℝ)+1≤(m:ℝ) := by exact_mod_cast j.isLt
    linarith [s.property.2]⟩

lemma meshTime_continuous {m : ℕ} (j : Fin m) : Continuous (meshTime j) := by
  apply Continuous.subtype_mk
  fun_prop

def meshSegment {m : ℕ} {L : Length} (j : Fin m) (ω : ConfigurationPath 1 L) : ConfigurationPath 1 L :=
  ⟨fun s ↦ ω (meshTime j s),ω.continuous.comp (meshTime_continuous j)⟩

lemma meshSegment_continuous {m : ℕ} (L : Length) (j : Fin m) :
    Continuous (meshSegment (L:=L) j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath 1 L×Time ↦ p.1 (meshTime j p.2))
  exact continuous_fst.eval ((meshTime_continuous j).comp continuous_snd)

@[simp] lemma meshSegment_one {L : Length} (ω : ConfigurationPath 1 L) :
    meshSegment (0:Fin 1) ω=ω := by
  apply ContinuousMap.ext
  intro s
  change ω (meshTime (0:Fin 1) s)=ω s
  congr 1
  apply Subtype.ext
  simp [meshTime]

lemma mesh_firstTime {m : ℕ} (hm : 0 < m) (s : Time) :
    meshTime (0:Fin (m+1)) s=prefixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) s := by
  apply Subtype.ext
  simp only [meshTime,Fin.val_zero,Nat.cast_zero,zero_add,prefixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  ring

lemma mesh_nextTime {m : ℕ} (hm : 0 < m) (j : Fin m) (s : Time) :
    meshTime j.succ s=suffixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) (meshTime j s) := by
  apply Subtype.ext
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hm1 : (1:ℝ)+m≠0 := by positivity
  simp only [meshTime,Fin.val_succ,suffixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

lemma meshSegment_first {m : ℕ} {L : Length} (hm : 0 < m) (ω : ConfigurationPath 1 L) :
    meshSegment (0:Fin (m+1)) ω=configurationPrefix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω := by
  ext s i j
  exact congrArg (fun u : Time ↦ ω u i j) (mesh_firstTime hm s)

lemma meshSegment_next {m : ℕ} {L : Length} (hm : 0 < m) (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j.succ ω=meshSegment j (configurationSuffix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (mesh_nextTime hm j s)

lemma meshTime_reverse {m : ℕ} (j : Fin m) (s : Time) :
    reverseTime (meshTime j s)=meshTime j.rev (reverseTime s) := by
  apply Subtype.ext
  have hm : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  change 1-((j:ℝ)+(s:ℝ))/(m:ℝ)=((j.rev:ℝ)+(1-(s:ℝ)))/(m:ℝ)
  have hj : (j.rev:ℝ)=(m:ℝ)-1-(j:ℝ) := by
    rw [Fin.val_rev,Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hj]
  field_simp
  ring

lemma meshSegment_reverse {m : ℕ} {L : Length} (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j (reverseConfigurationPath 1 L ω)=reverseConfigurationPath 1 L (meshSegment j.rev ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (meshTime_reverse j s)

lemma mesh_sum_reverse {m : ℕ} {L : Length} (F : ConfigurationPath 1 L→ℝ)
    (hF : ∀ω,F (reverseConfigurationPath 1 L ω)=F ω) (ω : ConfigurationPath 1 L) :
    ∑ j : Fin m,F (meshSegment j (reverseConfigurationPath 1 L ω))=
    ∑ j : Fin m,F (meshSegment j ω) := by
  simp only [meshSegment_reverse,hF]
  exact Equiv.sum_comp (Fin.revPerm) (fun j : Fin m ↦ F (meshSegment j ω))

end HardSphere.PathCutoff

end

end OAI
