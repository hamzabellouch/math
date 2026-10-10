import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalLegCollision

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def trialCutoffHit {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    (B : Set Point) (w : Time) (ω : ConfigurationPath 1 L) : Set (Point×(Noise×Noise)) :=
  {p | p.1∈B ∧ TrialCutoff L n r R C w S v (trialPath t y z p.1 p.2) ∧
    ∃s : Time,torusDistance L (projectPoint L (trialPath t y z p.1 p.2 s)) (ω s 0)≤r}

lemma trialCutoffHit_le {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z v : Point) (B : Set Point) (w : Time) (ω : ConfigurationPath 1 L)
    (hB : ∀u∈B,‖u-v‖≤3) (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hy : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hz : r+2*S<torusDistance L (projectPoint L z) (ω 1 0)) :
    ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S y z v B w ω)≤
      ((volume.restrict B).prod law) (torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ))+
      ((volume.restrict B).prod law) (torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ)) := by
  let A := torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ)
  let D := torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ)
  let f : Point×(Noise×Noise)→Point×Noise := fun p ↦ (p.1,pinned p.2.1)
  let g : Point×(Noise×Noise)→Point×Noise := fun p ↦ (p.1,pinned p.2.2)
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have hf : MeasurePreserving f ((volume.restrict B).prod (law.prod law)) ((volume.restrict B).prod law) :=
    (MeasurePreserving.id _).prod (hpin.comp (measurePreserving_fst (μ:=law) (ν:=law)))
  have hg : MeasurePreserving g ((volume.restrict B).prod (law.prod law)) ((volume.restrict B).prod law) :=
    (MeasurePreserving.id _).prod (hpin.comp (measurePreserving_snd (μ:=law) (ν:=law)))
  have hsub : trialCutoffHit n t r R C S y z v B w ω⊆f⁻¹' A∪g⁻¹' D := by
    rintro ⟨u,β⟩ ⟨hu,hcut,hit⟩
    exact trial_hit_cases y z u v B β w ω hu (hB u hu) hcut hω hy hz hit
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  exact add_le_add (hf.measure_preimage_le A) (hg.measure_preimage_le D)

lemma physical_trial_collision {L : Length} {m n : ℕ} (hn : 0<n)
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
    (hy : ∀i,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  apply (Finset.sum_le_sum (fun i _ ↦ trialCutoffHit_le (y i) (z i) v B w ω hBv hreg.2 (hy i) (hz i))).trans
  rw [Finset.sum_add_distrib]
  have h₁ := physical_leg_collision hn y v (configurationPrefix 1 L midpointTime ω) hL ht hr hr1
    (by norm_num : (0:ℝ)≤13) hε hR (by positivity : 0≤2*Creg) hh hsepY
    (prefix_mesh_regular hr.le ω hreg.1) hsmall hτr hnscale hwindow hlarge hdrift hBm hB hBY
  have h₂ := physical_leg_collision hn z v (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) hL ht hr hr1
    (by norm_num : (0:ℝ)≤13) hε hR (by positivity : 0≤2*Creg) hh hsepZ
    (prefix_mesh_regular hr.le _ ((meshRegular_reverse _ _ _ _ _).mpr hreg.1)) hsmall hτr hnscale hwindow hlarge hdrift hBm hB hBZ
  rw [hw]
  convert add_le_add h₁ h₂ using 1
  ring_nf

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma leg_lift_diameter_continuous (t : ℝ) (y u : Point) (w : Time) :
    Continuous (fun β : Noise ↦ liftedDiameter 0 w (pathCoordinates (leg t y u β))) := by
  apply (liftedDiameter_continuous 0 w).comp
  apply continuous_pi
  intro i
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ leg t y u p.1 p.2 i)
  have hl := leg_continuous t y u
  fun_prop

def GoodLeg (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) (β : Noise) : Prop :=
  LegMeshRegular n t r R C y u β ∧
    liftedDiameter 0 w (pathCoordinates (leg t y u β))≤S ∧
    incrementFluctuation t 1 0 1 β≤1/3

lemma goodLeg_measurable (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) :
    MeasurableSet {β | GoodLeg n t r R C S y u w β} :=
  (legMeshRegular_measurable n t r R C y u).inter
    ((measurableSet_le (leg_lift_diameter_continuous t y u w).measurable measurable_const).inter
      (measurableSet_le (incrementFluctuation_continuous t 1 0 1).measurable measurable_const))

lemma leg_failure_le (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) :
    law {β | ¬GoodLeg n t r R C S y u w β} ≤
      law {β | ¬LegMeshRegular n t r R C y u β}+
      law {β | S≤liftedDiameter 0 w (pathCoordinates (leg t y u β))}+
      law {β | (1/3:ℝ)≤ incrementFluctuation t 1 0 1 β} := by
  apply (measure_mono (show {β | ¬GoodLeg n t r R C S y u w β}⊆
    ({β | ¬LegMeshRegular n t r R C y u β} ∪ {β | S≤liftedDiameter 0 w (pathCoordinates (leg t y u β))}) ∪
      {β | (1/3:ℝ)≤ incrementFluctuation t 1 0 1 β} from ?_)).trans
  · exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  intro β hβ
  by_contra hn
  have hh := not_or.mp hn
  have hm := not_or.mp hh.1
  exact hβ ⟨not_not.mp hm.1,(le_of_not_ge hm.2),le_of_not_ge hh.2⟩

lemma trial_cutoff_failure (L : Length) (n : ℕ) {t r R C S : ℝ} (hr : 0<r)
    (y z u v : Point) (w : Time) (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3) :
    trialKernel t y z u {f | ¬TrialCutoff L n r R C w S v f}≤
      law {β | ¬GoodLeg n t r R C S y u w β}+
      law {β | ¬GoodLeg n t r R C S z u w β} := by
  have hcut : MeasurableSet {f | ¬TrialCutoff L n r R C w S v f} := (trialCutoff_measurable L n r R C w S v).compl
  have hm : Measurable (trialPath t y z u) := ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  rw [trialKernel_apply,Measure.map_apply hm hcut]
  let P := {β | ¬GoodLeg n t r R C S y u w β}
  let Q := {β | ¬GoodLeg n t r R C S z u w β}
  have hp : MeasurableSet P := (goodLeg_measurable n t r R C S y u w).compl
  have hq : MeasurableSet Q := (goodLeg_measurable n t r R C S z u w).compl
  have hpre : (trialPath t y z u) ⁻¹' {f | ¬TrialCutoff L n r R C w S v f}⊆
      (fun β : Noise×Noise ↦ pinned β.1) ⁻¹' P ∪ (fun β : Noise×Noise ↦ pinned β.2) ⁻¹' Q := by
    intro β hβ
    by_contra hn
    have hh := not_or.mp hn
    have h₁ : GoodLeg n t r R C S y u w (pinned β.1) := not_not.mp hh.1
    have h₂ : GoodLeg n t r R C S z u w (pinned β.2) := not_not.mp hh.2
    exact hβ (trial_cutoff_of_legs L hr y z u v β w hy hz hu h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2)
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have h₁ := hpin.comp (measurePreserving_fst (μ:=law) (ν:=law))
  have h₂ := hpin.comp (measurePreserving_snd (μ:=law) (ν:=law))
  exact ((measure_mono hpre).trans (measure_union_le _ _)).trans_eq
    (congrArg₂ (·+·) (h₁.measure_preimage hp.nullMeasurableSet) (h₂.measure_preimage hq.nullMeasurableSet))

lemma trial_cutoff_physical_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀R : ℝ,0≤R → wiener {β | R≤‖β‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0<n) {t r R B C S : ℝ}
    (ht : 0<t) (hr : 0<r) (hτr : t/(n:ℝ)≤r^2) (hR : 0≤R) (hB : 0≤B) (hC : 0≤C) (hS : 0<S)
    (y z u v : Point) (w : Time) (p : ℕ) (hp : p≠0)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (hdu : ‖u-y‖≤C) (hdz : ‖u-z‖≤C)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ)≤r) (hsmall : R*r<L.val/2)
    (hwindow : (w:ℝ)*C≤S/12) :
    trialKernel t y z u {f | ¬TrialCutoff L n r (3*(1+R)) (64*(meanCost+1)) w S v f}≤
      2*((n:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
        ENNReal.ofReal (Real.exp (-(n:ℝ)/((1+R)^3)))+
        3*(M*ENNReal.ofReal (Real.exp (-c*B^2)))+
        ENNReal.ofReal (scaleMoment p t S 0 w)/(ENNReal.ofReal (1/12:ℝ))^p+
        ENNReal.ofReal (scaleMoment p t 1 0 1)/(ENNReal.ofReal (1/3:ℝ))^p) := by
  apply (trial_cutoff_failure L n hr y z u v w hy hz hu).trans
  have h (x : Point) (hx : ‖u-x‖≤C) := (leg_failure_le n t r (3*(1+R)) (64*(meanCost+1)) S x u w).trans
    (add_le_add (add_le_add (strong_leg_mesh_tail htail L n hn ht hr hτr hR hB x u hx hdrift hsmall)
      (leg_window_tail ht.le hS hC x u hx w hwindow p hp))
      (incrementFluctuation_scale_tail (r:=1) (R:=1/3) ht.le (by norm_num) (by norm_num) 0 1 p hp))
  exact (add_le_add (h y hdu) (h z hdz)).trans_eq (by rw [two_mul])

end HardSphere.Bridge

end
end

end

end OAI
