import Mathlib
import OAI.Analysis.HardSphere.Bridges.CollisionBudget

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma meshInterval_diameter {L : Length} {n : ℕ} (j : Fin n) (ω : ConfigurationPath 1 L) :
    intervalDiameter (meshTime j 0) (meshTime j 1) ω=intervalDiameter 0 1 (meshSegment j ω) := by
  unfold intervalDiameter
  congr 1
  ext p
  change torusDistance L (ω (intervalTime (meshTime j 0) (meshTime j 1) p.1) 0)
    (ω (intervalTime (meshTime j 0) (meshTime j 1) p.2) 0)=_
  simp only [mesh_interval_time,meshSegment]
  have he (s : Time) : intervalTime 0 1 s=s := by apply Subtype.ext; simp [intervalTime]
  simp only [diameterMap,ContinuousMap.coe_mk,he]

lemma meshRemainder_early_bound {n : ℕ} (j : Fin n) (hj : (meshTime j 0:ℝ)≤1/2) :
    (meshRemainder j:ℝ)≤2/(n:ℝ) := by
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  have h := mesh_remaining j
  have hnon := (meshRemainder j).property.1
  have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)/2≤1-(meshTime j 0:ℝ) by linarith) hnon
  rw [h] at hh
  have he : (2:ℝ)/(n:ℝ)=2*(1/(n:ℝ)) := by ring
  rw [he]
  linarith

lemma physical_leg_collision {L : Length} {m n : ℕ} (hn : 0<n)
    (y : Fin m→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r C ε h R Creg : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hC : 0≤C) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h)
    (hsep : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hreg : MeshRegular n r R Creg ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*C/(n:ℝ)≤r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i u,u∈B → ‖u-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (torusLegHit t (y i) v B ω r C (h/t)))≤
      ENNReal.ofReal (hitConstant*(4*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter (fun j ↦ h/(2*t)≤(meshTime j 0:ℝ))
  let A : Fin n→ℝ := fun j ↦ diameterRatio r (meshSegment j ω)
  have hI j (hj : j∈I) : h/(2*t)≤(meshTime j 0:ℝ) := (Finset.mem_filter.mp hj).2
  have hA0 j : 0≤A j := diameterRatio_nonneg hr.le _
  have hAsum : (∑j∈I,(1+A j)^3)≤2*Creg*(n:ℝ) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ ↦ by have := hA0 j; positivity)).trans
    exact hreg.2.trans (by nlinarith)
  have hdi j : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤r*A j := by
    rw [meshInterval_diameter]
    dsimp [A,diameterRatio]
    rw [mul_div_cancel₀ _ hr.ne']
  have hd1 : C/(n:ℝ)≤r := (div_le_div_of_nonneg_right (by linarith : C≤2*C) (by positivity)).trans hdrift
  have hh' := torusLegHit_sum hn (endpointIndex_pos ht hlarge) y v I ω A hL ht hr hr1 hC hε hR hsep
    (fun j q hq ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,mesh_endpoint_index j q ht hwindow hq⟩)
    (fun j hj ↦ endpointIndex_gap j ht hh (hI j hj))
    (fun j _ ↦ hA0 j) (fun j _ ↦ hreg.1 j) hAsum
    (fun j _ ↦ (mul_le_mul_of_nonneg_left (hreg.1 j) hr.le).trans hsmall)
    (fun j _ ↦ hdi j)
    (fun j _ hj ↦ (mul_le_mul_of_nonneg_right (meshRemainder_early_bound j hj) hC).trans (by simpa [div_mul_eq_mul_div] using hdrift))
    hτr hd1 hBm hB hBdist
  apply hh'.trans
  apply ENNReal.ofReal_le_ofReal
  apply mesh_collision_budget hn ht hr hε hCreg hR (by positivity) hnscale
  have hs := endpointIndex_scale hn ht hlarge
  simpa only [div_div,show (2:ℝ)*4=8 by norm_num] using hs

end HardSphere.Bridge

end
end

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace HardSphere.Bridge
open Wiener PathCutoff

lemma interval_start_displacement {L : Length} (ω : ConfigurationPath 1 L) (w s : Time)
    (hs : (s:ℝ)≤(w:ℝ)) :
    torusDistance L (ω s 0) (ω 0 0)≤ intervalDiameter 0 w ω := by
  by_cases hw : (w:ℝ)=0
  · have hs0 : s=0 := Subtype.ext (by simpa using le_antisymm (hs.trans_eq hw) s.property.1)
    rw [hs0]
    have he : torusDistance L (ω 0 0) (ω 0 0)=0 := by simp [torusDistance]
    rw [he]
    exact intervalDiameter_nonneg _ _ _
  have hwpos : 0<(w:ℝ) := lt_of_le_of_ne w.property.1 (Ne.symm hw)
  let q : Time := ⟨(s:ℝ)/(w:ℝ),⟨div_nonneg s.property.1 w.property.1,(div_le_one hwpos).mpr hs⟩⟩
  have hq : intervalTime 0 w q=s := by
    apply Subtype.ext
    change (1-(s:ℝ)/(w:ℝ))*0+((s:ℝ)/(w:ℝ))*(w:ℝ)=(s:ℝ)
    simp only [mul_zero,zero_add,div_mul_cancel₀ _ hw]
  simpa only [hq,intervalTime_zero] using intervalDistance_le 0 w q 0 ω

lemma no_collision_endpoint_window {L : Length} {r S : ℝ} (ω ζ : ConfigurationPath 1 L)
    (w : Time) (hω : intervalDiameter 0 w ω≤ S) (hζ : intervalDiameter 0 w ζ≤ S)
    (hsep : r+2*S< torusDistance L (ω 0 0) (ζ 0 0))
    (s : Time) (hs : (s:ℝ)≤(w:ℝ)) :
    r< torusDistance L (ω s 0) (ζ s 0) := by
  have h₁ := (interval_start_displacement ω w s hs).trans hω
  have h₂ := (interval_start_displacement ζ w s hs).trans hζ
  have ht₁ := torusDistance_triangle' L (ω 0 0) (ω s 0) (ζ 0 0)
  have ht₂ := torusDistance_triangle' L (ω s 0) (ζ s 0) (ζ 0 0)
  rw [torusDistance_comm L (ω 0 0) (ω s 0)] at ht₁
  linarith

lemma collision_after_window {L : Length} {r S : ℝ} (ω ζ : ConfigurationPath 1 L)
    (w : Time) (hω : intervalDiameter 0 w ω≤ S) (hζ : intervalDiameter 0 w ζ≤ S)
    (hsep : r+2*S< torusDistance L (ω 0 0) (ζ 0 0))
    (s : Time) (hit : torusDistance L (ω s 0) (ζ s 0)≤ r) :
    (w:ℝ)<(s:ℝ) := by
  by_contra hn
  exact (not_lt_of_ge hit) (no_collision_endpoint_window ω ζ w hω hζ hsep s (le_of_not_gt hn))

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma prefix_mesh_half {L : Length} {n : ℕ} (j : Fin n) (ω : ConfigurationPath 1 L) :
    meshSegment j (configurationPrefix 1 L midpointTime ω)=meshSegment (j.castAdd n) ω := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply,mesh_first_half]

lemma prefix_mesh_regular {L : Length} {n : ℕ} {r R C : ℝ} (hr : 0≤r) (ω : ConfigurationPath 1 L)
    (h : MeshRegular (n+n) r R C ω) :
    MeshRegular n r R (2*C) (configurationPrefix 1 L midpointTime ω) := by
  constructor
  · intro j
    rw [prefix_mesh_half]
    exact h.1 (j.castAdd n)
  · simp_rw [prefix_mesh_half]
    have hs := h.2
    rw [Fin.sum_univ_add] at hs
    have hn : 0≤∑j : Fin n,cubicCost r (meshSegment (j.natAdd n) ω) :=
      Finset.sum_nonneg (fun j _ ↦ cubicCost_nonneg hr _)
    push_cast at hs
    nlinarith

lemma prefix_window_diameter {L : Length} (ω : ConfigurationPath 1 L) (w : Time) :
    intervalDiameter 0 w (configurationPrefix 1 L midpointTime ω)=
      intervalDiameter 0 (prefixTime midpointTime w) ω := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  have he (s : Time) : prefixTime midpointTime (intervalTime 0 w s)=intervalTime 0 (prefixTime midpointTime w) s := by
    apply Subtype.ext
    simp [prefixTime,intervalTime,midpointTime]
    ring
  change torusDistance L (ω (prefixTime midpointTime (intervalTime 0 w p.1)) 0)
    (ω (prefixTime midpointTime (intervalTime 0 w p.2)) 0)=_
  rw [he,he]
  rfl

lemma trial_initial_projection (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    configurationPrefix 1 L midpointTime (projectCurve L (trialPath t y z u β))=
      projectCurve L (leg t y u (pinned β.1)) := by
  apply ContinuousMap.ext
  intro s
  simp only [configurationPrefix,projectCurve,ContinuousMap.coe_mk,ContinuousMap.comp_apply,trial_left]

lemma trial_hit_first {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (B : Set Point) (β : Noise×Noise) (w q : Time) (ω : ConfigurationPath 1 L)
    (hu : u∈B) (huv : ‖u-v‖≤3)
    (hf : TrialCutoff L n r R C w S v (trialPath t y z u β))
    (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hsep : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hit : torusDistance L (projectPoint L (trialPath t y z u β (prefixTime midpointTime q)))
      (ω (prefixTime midpointTime q) 0)≤r) :
    (u,pinned β.1)∈torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ) := by
  have htreg : intervalDiameter 0 w (projectCurve L (leg t y u (pinned β.1)))≤S := by
    rw [←trial_initial_projection,prefix_window_diameter]
    exact hf.1.2.1
  have how : intervalDiameter 0 w (configurationPrefix 1 L midpointTime ω)≤S := by
    rw [prefix_window_diameter]
    exact hω.1
  have hs := collision_after_window (projectCurve L (leg t y u (pinned β.1)))
    (configurationPrefix 1 L midpointTime ω) w htreg how
    (by simpa only [projectCurve,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply,pinned_leg_zero,
      show prefixTime midpointTime 0=0 by apply Subtype.ext; simp [prefixTime]] using hsep) q
    (by simpa only [trial_left,projectCurve,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply] using hit)
  refine ⟨hu,?_,?_,q,hs.le,?_⟩
  · intro s
    simpa only [trial_left] using hf.2 (prefixTime midpointTime s)
  · intro s
    have hc := (hf.2 (prefixTime midpointTime s)).1
    rw [trial_left] at hc
    have hvu : ‖v-u‖≤3 := by simpa only [norm_sub_rev] using huv
    exact (norm_sub_le_norm_sub_add_norm_sub (leg t y u (pinned β.1) s) v u).trans (by linarith)
  · simpa only [trial_left,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply] using hit

lemma reverse_suffix_midpoint (q : Time) :
    reverseTime (suffixTime midpointTime q)=prefixTime midpointTime (reverseTime q) := by
  apply Subtype.ext
  change 1-((1/2:ℝ)+(1-1/2)*(q:ℝ))=(1/2)*(1-(q:ℝ))
  ring

lemma trialCutoff_reverse {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (β : Noise×Noise) (w : Time) :
    TrialCutoff L n r R C w S v (trialPath t z y u β.swap) ↔
    TrialCutoff L n r R C w S v (trialPath t y z u β) := by
  have hf : ∀s : Time,trialPath t z y u β.swap s=trialPath t y z u β (reverseTime s) := by
    intro s
    have hs := congrArg (fun ω : ConfigurationPath 1 L ↦ ω s 0) (trial_reverse L t y z u β)

    have h₁ : leftTime (reverseTime s)=reverseTime (rightTime s) := by
      apply Subtype.ext
      change min (2*(1-(s:ℝ))) 1=1-max (2*(s:ℝ)-1) 0
      by_cases hh : (s:ℝ)≤1/2
      · rw [min_eq_right (by linarith),max_eq_right (by linarith)]; ring
      · rw [min_eq_left (by linarith),max_eq_left (by linarith)]; ring
    have h₂ : reverseTime (rightTime (reverseTime s))=leftTime s := by
      apply Subtype.ext
      change 1-max (2*(1-(s:ℝ))-1) 0=min (2*(s:ℝ)) 1
      by_cases hh : (s:ℝ)≤1/2
      · rw [max_eq_left (by linarith),min_eq_left (by linarith)]; ring
      · rw [max_eq_right (by linarith),min_eq_right (by linarith)]; ring
    simp only [trialPath,ContinuousMap.coe_mk,h₁,h₂,Prod.fst_swap,Prod.snd_swap]
    abel
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [←trial_reverse,regular_reverse]
  apply and_congr_right
  intro _
  unfold TrialConfined
  constructor
  · intro h s
    simpa only [hf,reverseTime_reverse] using h (reverseTime s)
  · intro h s
    rw [hf]
    exact h (reverseTime s)

lemma trial_hit_cases {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (B : Set Point) (β : Noise×Noise) (w : Time) (ω : ConfigurationPath 1 L)
    (hu : u∈B) (huv : ‖u-v‖≤3)
    (hf : TrialCutoff L n r R C w S v (trialPath t y z u β))
    (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hy : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hz : r+2*S<torusDistance L (projectPoint L z) (ω 1 0))
    (hit : ∃s : Time,torusDistance L (projectPoint L (trialPath t y z u β s)) (ω s 0)≤r) :
    (u,pinned β.1)∈torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ) ∨
    (u,pinned β.2)∈torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ) := by
  obtain ⟨s,hs⟩ := hit
  rcases prefix_or_suffix s with ⟨q,rfl⟩|⟨q,rfl⟩
  · exact Or.inl (trial_hit_first y z u v B β w q ω hu huv hf hω hy hs)
  · apply Or.inr
    apply trial_hit_first z y u v B β.swap w (reverseTime q) (reverseConfigurationPath 1 L ω) hu huv
      ((trialCutoff_reverse y z u v β w).mpr hf) ((endpointRegular_reverse _ _ _).mpr hω)
      (by simpa only [reverseConfigurationPath,ContinuousMap.coe_mk,ContinuousMap.comp_apply,reverseTime_zero] using hz)
    have ht : reverseTime (prefixTime midpointTime (reverseTime q))=suffixTime midpointTime q := by
      rw [←reverse_suffix_midpoint,reverseTime_reverse]
    simpa only [trial_left,Prod.fst_swap,trial_right,reverseConfigurationPath,ContinuousMap.coe_mk,ContinuousMap.comp_apply,ht] using hs

end HardSphere.Bridge

end
end

end

end OAI
