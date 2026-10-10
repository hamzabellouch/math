import Mathlib
import OAI.Analysis.HardSphere.Bridges.TrialHitMeasure

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

def TrialCollision {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) (f : C(Time,Point)) : Prop :=
  ∃s : Time,torusDistance L (projectPoint L (f s)) (ω s 0)≤r

lemma trialCollision_closed {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    IsClosed {f | TrialCollision r ω f} := by
  let E : Set (C(Time,Point)×Time) := {p | torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0)≤r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : C(Time,Point)×Time ↦
      (projectPoint L (p.1 p.2),ω p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : C(Time,Point)×Time ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
      fun_prop
    · exact (continuous_apply 0).comp (ω.continuous.comp continuous_snd)
  convert isClosedMap_fst_of_compactSpace E hE using 1
  ext f
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(f,s),hs,rfl⟩,fun ⟨⟨g,s⟩,hs,hg⟩ ↦ by
    change g=f at hg
    subst g
    exact ⟨s,hs⟩⟩

lemma trialCutoffHit_measurable {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    {B : Set Point} (hB : MeasurableSet B) (w : Time) (ω : ConfigurationPath 1 L) :
    MeasurableSet (trialCutoffHit n t r R C S y z v B w ω) := by
  have hm := (trialPath_continuous t y z).measurable
  exact (hB.preimage measurable_fst).inter
    (((trialCutoff_measurable L n r R C w S v).preimage hm).inter
      ((trialCollision_closed r ω).measurableSet.preimage hm))

lemma trialCutoffHit_integral {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    {B : Set Point} (hB : MeasurableSet B) (w : Time) (ω : ConfigurationPath 1 L) :
    (∫⁻u in B,trialKernel t y z u {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r ω f})=
      ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S y z v B w ω) := by
  rw [Measure.prod_apply (trialCutoffHit_measurable n t r R C S y z v hB w ω)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hB] with u hu
  have hm : Measurable (trialPath t y z u) := ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  have hA : MeasurableSet {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r ω f} :=
    (trialCutoff_measurable L n r R C w S v).inter (trialCollision_closed r ω).measurableSet
  rw [trialKernel_apply,Measure.map_apply hm hA]
  congr 1
  ext β
  simp only [mem_preimage,mem_ofPred_eq,trialCutoffHit,TrialCollision,hu,true_and]

def TrialSuccess {L : Length} {k : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin k→ ConfigurationPath 1 L) : Set C(Time,Point) :=
  {f | TrialCutoff L n r R C w S v f ∧ ∀j,¬TrialCollision r (ω j) f}

lemma trialSuccess_measurable {L : Length} {k : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin k→ ConfigurationPath 1 L) : MeasurableSet (TrialSuccess n r R C S w v ω) := by
  have h : MeasurableSet {f | ∀j,¬TrialCollision r (ω j) f} := by
    simpa only [ofPred_forall,Set.compl_ofPred] using MeasurableSet.iInter (fun j ↦ (trialCollision_closed r (ω j)).measurableSet.compl)
  exact (trialCutoff_measurable L n r R C w S v).inter h

lemma trial_success_failure_le {L : Length} {k : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time) (y z v u : Point)
    (ω : Fin k→ ConfigurationPath 1 L) :
    trialKernel t y z u (TrialSuccess n r R C S w v ω)ᶜ≤
      trialKernel t y z u {f | ¬TrialCutoff L n r R C w S v f}+
        ∑j,trialKernel t y z u {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f} := by
  have hsub : (TrialSuccess n r R C S w v ω)ᶜ⊆
      {f | ¬TrialCutoff L n r R C w S v f} ∪ ⋃j,{f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f} := by
    intro f hf
    by_cases hc : TrialCutoff L n r R C w S v f
    · right
      have hh : ¬∀j,¬TrialCollision r (ω j) f := fun hh ↦ hf ⟨hc,hh⟩
      push Not at hh
      obtain ⟨j,hj⟩ := hh
      exact mem_iUnion.mpr ⟨j,hc,hj⟩
    · exact Or.inl hc
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (measure_iUnion_fintype_le _ _))

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma physical_trial_collision_fintype {L : Length} {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0<n)
    (y z : ι→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r ε h R Creg S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : Regular (n+n) r R Creg (prefixTime midpointTime w) S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ)≤r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀i,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(Fintype.card ι:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hp := physical_trial_collision hn (fun i ↦ y (e i)) (fun i ↦ z (e i)) v ω w hL ht hr hr1 hε
    hR hCreg hh hw (fun i j hij ↦ hsepY (e i) (e j) (e.injective.ne hij))
    (fun i j hij ↦ hsepZ (e i) (e j) (e.injective.ne hij)) hreg hsmall hτr hnscale hwindow hlarge hdrift
    hBm hB hBv (fun i ↦ hBY (e i)) (fun i ↦ hBZ (e i)) (fun i ↦ hy (e i)) (fun i ↦ hz (e i))
  let f : ι → ℝ≥0∞ := fun i ↦ ((volume.restrict B).prod (law.prod law))
    (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω)
  change (∑ i, f (e i)) ≤ _ at hp
  rw [e.sum_comp] at hp
  exact hp

lemma physical_trial_collision_subset {L : Length} {m n : ℕ} (hn : 0<n) (I : Finset (Fin m))
    (y z : Fin m→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r ε h R Creg S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : Regular (n+n) r R Creg (prefixTime midpointTime w) S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ)≤r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀i∈I,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i∈I,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i∈I,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  have hp := physical_trial_collision_fintype (ι:=I) hn (fun i ↦ y i) (fun i ↦ z i) v ω w hL ht hr hr1 hε
    hR hCreg hh hw (fun i j hij ↦ hsepY i j (fun he ↦ hij (Subtype.ext he)))
    (fun i j hij ↦ hsepZ i j (fun he ↦ hij (Subtype.ext he))) hreg hsmall hτr hnscale hwindow hlarge hdrift
    hBm hB hBv (fun i ↦ hBY i) (fun i ↦ hBZ i) (fun i ↦ hy i i.property) (fun i ↦ hz i i.property)
  let f : Fin m → ℝ≥0∞ := fun i ↦ ((volume.restrict B).prod (law.prod law))
    (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω)
  change (∑ i : I, f i) ≤ _ at hp
  rw [Fintype.card_coe,Finset.sum_coe_sort] at hp
  apply hp.trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  have hcard : (I.card:ℝ) ≤ m := by exact_mod_cast (Finset.card_le_card (Finset.subset_univ I)).trans_eq (by simp)
  have hk := hitConstant_pos.le
  gcongr

end HardSphere.Bridge

end
end

end

end OAI
