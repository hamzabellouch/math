import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSuccess
import OAI.Analysis.HardSphere.Bridges.LocalReference
import OAI.Analysis.HardSphere.Bridges.EarlyTorusHit

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma earlyTorusHit_measurable {L : Length} (t : ℝ) (y z v : Point)
    (ω : ConfigurationPath 1 L) (r C h : ℝ) : MeasurableSet (earlyTorusHit t y z v ω r C h) := by
  let E : Set (C(Time,Point)×Time) := {p | h≤(p.2:ℝ) ∧ (p.2:ℝ)≤1/2 ∧
    torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0)≤r}
  have hc : Continuous (fun p : C(Time,Point)×Time ↦
      torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0)) := by
    apply (torusDistance_continuous_pair L).comp (f := fun p : C(Time,Point)×Time ↦
      (projectPoint L (p.1 p.2),ω p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : C(Time,Point)×Time ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
      fun_prop
    · exact (continuous_apply 0).comp (ω.continuous.comp continuous_snd)
  have hE : IsClosed E := by
    change IsClosed ({p : C(Time,Point)×Time | h≤(p.2:ℝ)} ∩
      ({p | (p.2:ℝ)≤1/2} ∩ {p | torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0)≤r}))
    exact (isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_le (by fun_prop) continuous_const).inter (isClosed_le hc continuous_const))
  have hhit : IsClosed {f : C(Time,Point) | ∃s : Time,h≤(s:ℝ) ∧ (s:ℝ)≤1/2 ∧
      torusDistance L (projectPoint L (f s)) (ω s 0)≤r} := by
    convert isClosedMap_fst_of_compactSpace E hE using 1
    ext f
    simp only [mem_ofPred_eq,mem_image,E]
    exact ⟨fun ⟨s,hs⟩ ↦ ⟨(f,s),hs,rfl⟩,fun ⟨⟨g,s⟩,hs,hg⟩ ↦ by
      change g=f at hg
      subst g
      exact ⟨s,hs⟩⟩
  have hnorm : IsClosed {f : C(Time,Point) | ∀s : Time,‖f s-z‖≤C} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun s ↦ isClosed_le ((continuous_eval_const s).sub continuous_const).norm continuous_const)
  exact (((trialConfined_measurable L v).inter (hnorm.measurableSet.inter hhit.measurableSet)).preimage
    (leg_continuous t y z).measurable)

lemma leg_reverse (t : ℝ) (y z : Point) (β : Noise) (s : Time) :
    leg t z y (reverseNoise β) s=leg t y z β (reverseTime s) := by
  ext j
  simp only [leg,ContinuousMap.coe_mk,mean,reverseNoise,bridgeReverse,
    ContinuousMap.compCLM_apply,ContinuousMap.comp_apply]
  change (1-(s:ℝ))*z j+(s:ℝ)*y j+_= (1-(1-(s:ℝ)))*y j+(1-(s:ℝ))*z j+_
  ring

lemma project_leg_reverse (L : Length) (t : ℝ) (y z : Point) (β : Noise) :
    projectCurve L (leg t z y (reverseNoise β)) =
      reverseConfigurationPath 1 L (projectCurve L (leg t y z β)) := by
  ext s i j
  change ((leg t z y (reverseNoise β) s) j : AddCircle L.val)=_
  rw [leg_reverse]
  rfl

lemma leg_endpoints_ae (t : ℝ) (y z : Point) :
    ∀ᵐβ ∂law,leg t y z β 0=y ∧ leg t y z β 1=z := by
  have he : ∀ᵐβ ∂law,∀j : Fin 3,β j 0=0 ∧ β j 1=0 := by
    exact ae_all_iff.mpr (fun j ↦ (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints)
  filter_upwards [he] with β hβ
  constructor <;> ext j <;> simp [leg,mean,(hβ j).1,(hβ j).2]

lemma reference_collision {L : Length} {n : ℕ} (hn : 0<n)
    (y z v : Point) (ω : ConfigurationPath 1 L) (w : Time) {t r S h R Creg : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hR : 0≤R)
    (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3)
    (hreg : Regular n r R Creg w S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 26/(n:ℝ)≤r)
    (hsep0 : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hsep1 : r+2*S<torusDistance L (projectPoint L z) (ω 1 0)) :
    (law.map (leg t y z)) {f | Regular n r R Creg w S (projectCurve L f) ∧
      TrialConfined L v f ∧ TrialCollision r ω f} ≤
      2*ENNReal.ofReal (hitConstant*(4*Creg*t*r+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  have hm : MeasurableSet {f : C(Time,Point) | Regular n r R Creg w S (projectCurve L f) ∧
      TrialConfined L v f ∧ TrialCollision r ω f} :=
    ((regular_measurable n r R Creg w S).preimage (projectCurve_continuous L).measurable).inter
      ((trialConfined_measurable L v).inter (trialCollision_closed r ω).measurableSet)
  rw [Measure.map_apply (leg_continuous t y z).measurable hm]
  let A := earlyTorusHit t y z v ω r 13 (h/t)
  let B := earlyTorusHit t z y v (reverseConfigurationPath 1 L ω) r 13 (h/t)
  have hu : {β | Regular n r R Creg w S (projectCurve L (leg t y z β)) ∧
      TrialConfined L v (leg t y z β) ∧ TrialCollision r ω (leg t y z β)} ≤ᵐ[law]
      (A ∪ reverseNoise ⁻¹' B : Set Noise) := by
    filter_upwards [leg_endpoints_ae t y z] with β hβ
    rintro ⟨hf,hconf,s,hit⟩
    have hbnd (e : Point) (he : ‖e-v‖≤3) (q : Time) : ‖leg t y z β q-e‖≤13 := by
      have he' : ‖v-e‖≤3 := by simpa only [norm_sub_rev] using he
      exact (norm_sub_le_norm_sub_add_norm_sub _ v _).trans (by linarith [(hconf q).1])
    by_cases hs : (s:ℝ)≤1/2
    · left
      refine ⟨hconf,hbnd z hz,s,?_,hs,hit⟩
      rw [←hw]
      exact (collision_after_window (projectCurve L (leg t y z β)) ω w hf.2.1 hreg.2.1
        (by simpa only [projectCurve,ContinuousMap.coe_mk,hβ.1] using hsep0) s hit).le
    · right
      have hf' := (regular_reverse n r R Creg w S (projectCurve L (leg t y z β))).mpr hf
      have hω' := (regular_reverse n r R Creg w S ω).mpr hreg
      have hhrev : torusDistance L ((reverseConfigurationPath 1 L (projectCurve L (leg t y z β))) (reverseTime s) 0)
          ((reverseConfigurationPath 1 L ω) (reverseTime s) 0)≤r := by simpa only [reverseConfigurationPath,ContinuousMap.comp_apply,reverseTime_reverse,projectCurve,ContinuousMap.coe_mk] using hit
      change reverseNoise β∈B
      refine ⟨(fun q ↦ by simpa only [leg_reverse] using hconf (reverseTime q)),
        (fun q ↦ by simpa only [leg_reverse] using hbnd y hy (reverseTime q)),reverseTime s,?_,?_,?_⟩
      · rw [←hw]
        exact (collision_after_window _ _ w hf'.2.1 hω'.2.1
          (by simpa only [reverseConfigurationPath,ContinuousMap.comp_apply,reverseTime_zero,projectCurve,ContinuousMap.coe_mk,hβ.2] using hsep1)
          (reverseTime s) hhrev).le
      · change 1-(s:ℝ)≤1/2
        linarith
      · simpa only [leg_reverse,reverseTime_reverse,reverseConfigurationPath,ContinuousMap.comp_apply,projectCurve,ContinuousMap.coe_mk] using hhrev
  apply ((measure_mono_ae hu).trans (measure_union_le _ _)).trans
  have hrev : law (reverseNoise ⁻¹' B)=law B := reverseNoise_preserving.measure_preimage (earlyTorusHit_measurable t z y v _ r 13 (h/t)).nullMeasurableSet
  rw [hrev,two_mul]
  apply add_le_add
  · exact physical_early_collision hn y z v ω hL ht hr hr1 (by norm_num) hR hCreg hh hreg.1 hsmall hτr hnscale hwindow hlarge (by simpa only [show (2:ℝ)*13=26 by norm_num] using hdrift)
  · exact physical_early_collision hn z y v _ hL ht hr hr1 (by norm_num) hR hCreg hh
      ((meshRegular_reverse n r R Creg ω).mpr hreg.1) hsmall hτr hnscale hwindow hlarge (by simpa only [show (2:ℝ)*13=26 by norm_num] using hdrift)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma individual_normalizer_lower {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    c*(volume A*midpointLower t C)≤(law.map (leg (2*t) y z)) S := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have h₁ : c≤∫⁻u,trialKernel t y z u S ∂targetUniform A := by
    calc
      _ = ∫⁻_u,c ∂targetUniform A := by simp
      _ ≤ _ := lintegral_mono_ae hc
  have h₂ : (∫⁻u,trialKernel t y z u S ∂targetUniform A)≤
      ((volume A)⁻¹*(midpointLower t C)⁻¹)*(∫⁻u,trialKernel t y z u S ∂midpointLaw t y z) := by
    convert lintegral_mono' (targetUniform_le_midpoint ht hC y z hA hbound)
      (f:=fun u ↦ trialKernel t y z u S) le_rfl using 1
    rw [lintegral_smul_measure,smul_eq_mul]
  have he : (∫⁻u,trialKernel t y z u S ∂midpointLaw t y z)=(law.map (leg (2*t) y z)) S := by
    rw [←full_bridge_midpoint ht.le y z,Measure.map_apply measurable_snd hS,
      Measure.compProd_apply (hS.preimage measurable_snd)]
    rfl
  have h := mul_le_mul_right (h₁.trans h₂) (volume A*midpointLower t C)
  have hcancel : (volume A*midpointLower t C)*((volume A)⁻¹*(midpointLower t C)⁻¹)=1 := by
    rw [mul_mul_mul_comm,ENNReal.mul_inv_cancel hA0 hAfinite,
      ENNReal.mul_inv_cancel (midpointLower_pos ht C).ne' (midpointLower_ne_top t C),one_mul]
  rw [←mul_assoc,hcancel,one_mul,he] at h
  simpa only [mul_comm c] using h

lemma normalized_collision_le {X : Type*} [MeasurableSpace X] (P : Measure X)
    (S C A : Set X) (hC : MeasurableSet C) (hsub : C∩S⊆A) {a b : ℝ≥0∞}
    (ha : a≤P S) (hb : P A≤b) :
    ((P S)⁻¹ • P.restrict S) C≤a⁻¹*b := by
  rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hC]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr ha) ((measure_mono hsub).trans hb)

end HardSphere.Bridge

end
end

end

end OAI
