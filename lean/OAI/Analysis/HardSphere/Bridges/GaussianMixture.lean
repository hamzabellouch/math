import Mathlib
import OAI.Analysis.HardSphere.Bridges.ReverseTime
import OAI.Analysis.HardSphere.Bridges.GaussianDensity

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma gaussian_sum_density {m : ℕ} (q : Fin m → Point) {v : ℝ≥0} (hv : v≠0) :
    (∑i,Measure.pi (fun j : Fin 3 ↦ gaussianReal (q i j) v))=
    (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (∑i,density ((2*(v:ℝ))⁻¹) (x-q i))) := by
  simp_rw [gaussian_pi_eq (q _) hv]
  have hm (i : Fin m) : Measurable (fun x : Point ↦ ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q i))) :=
    ((density_continuous _).measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hw := withDensity_tsum (μ:=(volume : Measure Point)) hm
  rw [←Measure.sum_fintype,←hw]
  congr 1
  funext x
  rw [tsum_fintype]
  simp only [Finset.sum_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ density_nonneg _ _)).symm

lemma gaussian_sum_le {m : ℕ} (q : Fin m → Point) {v : ℝ≥0} (hv : v≠0)
    {ε : ℝ} (hε : 0<ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,Measure.pi (fun j : Fin 3 ↦ gaussianReal (q i j) v)) ≤
      ENNReal.ofReal (packingConstant*(ε⁻¹^3+(Real.sqrt ((2*(v:ℝ))⁻¹))^3)) • (volume : Measure Point) := by
  have hvp : 0<(v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [gaussian_sum_density q hv,←withDensity_const]
  exact withDensity_mono (Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal
    (density_packing q x (by positivity) hε hsep))

lemma scaled_separated {m : ℕ} (q : Fin m → Point) (u : Point) {a ε : ℝ}
    (ha : 0≤a) (hε : 0≤ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    ∀i j,i≠j → (a*ε)^2 ≤ square ((fun k ↦ a*q i k+(1-a)*u k)-(fun k ↦ a*q j k+(1-a)*u k)) := by
  intro i j hij
  have he : square ((fun k ↦ a*q i k+(1-a)*u k)-(fun k ↦ a*q j k+(1-a)*u k))=a^2*square (q i-q j) := by
    unfold square
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Pi.sub_apply]
    ring
  rw [he,mul_pow]
  exact mul_le_mul le_rfl (hsep i j hij) (pow_nonneg hε 2) (pow_nonneg ha 2)

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def mean (y u : Point) (s : Time) : Point := fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*u j
def leg (t : ℝ) (y u : Point) (β : Noise) : C(Time,Point) :=
  ⟨fun s j ↦ mean y u s j+Real.sqrt (2*t)*β j s,by unfold mean; fun_prop⟩
lemma leg_continuous (t : ℝ) (y u : Point) : Continuous (leg t y u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ fun j ↦ mean y u p.2 j+Real.sqrt (2*t)*p.1 j p.2)
  unfold mean
  fun_prop
lemma leg_eval_measurable (t : ℝ) (y u : Point) (s : Time) : Measurable (fun β ↦ leg t y u β s) :=
  (show Continuous (fun β : Noise ↦ leg t y u β s) from (continuous_eval_const s).comp (leg_continuous t y u)).measurable

def legVariance (t : ℝ) (s : Time) : ℝ≥0 := (NNReal.mk ((Real.sqrt (2*t))^2) (sq_nonneg _))*variance s
lemma variance_val (s : Time) : (variance s : ℝ)=(s:ℝ)*(1-(s:ℝ)) := by
  have hp : 0≤(s:ℝ)-(s:ℝ)^2 := by nlinarith [s.property.1,s.property.2]
  rw [variance,Real.coe_toNNReal _ hp]
  ring
lemma legVariance_val {t : ℝ} (ht : 0≤t) (s : Time) : (legVariance t s : ℝ)=2*t*(s:ℝ)*(1-(s:ℝ)) := by
  change (Real.sqrt (2*t))^2*(variance s : ℝ)=_
  rw [Real.sq_sqrt (by positivity),variance_val]
  ring
lemma legVariance_pos {t : ℝ} (ht : 0<t) {s : Time} (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)<1) :
    0<legVariance t s := by
  rw [←NNReal.coe_pos,legVariance_val ht.le]
  positivity

lemma position_law (t : ℝ) (y u : Point) (s : Time) :
    law.map (fun β ↦ leg t y u β s)=Measure.pi (fun j ↦ gaussianReal (mean y u s j) (legVariance t s)) := by
  have hs : HasLaw (fun β : C(Time,ℝ) ↦ β s) (gaussianReal 0 (variance s)) bridgeLaw :=
    ⟨(continuous_eval_const s).measurable.aemeasurable,scalar_eval s⟩
  unfold law
  change (Measure.pi (fun _ : Fin 3 ↦ bridgeLaw)).map
    (fun β j ↦ mean y u s j+Real.sqrt (2*t)*β j s)=_
  rw [Measure.pi_map_pi (f:=fun j (β : C(Time,ℝ)) ↦ mean y u s j+Real.sqrt (2*t)*β s)
    (fun j ↦ (gaussianReal_const_add (gaussianReal_const_mul hs (Real.sqrt (2*t))) (mean y u s j)).aemeasurable)]
  congr 1
  funext j
  simpa only [mul_zero,zero_add,legVariance] using
    (gaussianReal_const_add (gaussianReal_const_mul hs (Real.sqrt (2*t))) (mean y u s j)).map_eq

lemma position_independent (t : ℝ) (y u : Point) (s : Time) :
    IndepFun (fun β ↦ leg t y u β s) (remainder s) law := by
  have hi := (independent s).comp
    (show Measurable (fun x : Point ↦ fun j ↦ mean y u s j+Real.sqrt (2*t)*x j) from by fun_prop) measurable_id
  exact hi

lemma position_joint (t : ℝ) (y u : Point) (s : Time) :
    law.map (fun β ↦ (remainder s β,leg t y u β s))=
      (law.map (remainder s)).prod (Measure.pi (fun j ↦ gaussianReal (mean y u s j) (legVariance t s))) := by
  rw [(position_independent t y u s).symm.map_prod_eq_prod_map_map (remainder_measurable s).aemeasurable
    (leg_eval_measurable t y u s).aemeasurable,position_law]

lemma mean_separated {m : ℕ} (y : Fin m → Point) (u : Point) (s : Time) {ε : ℝ} (hε : 0≤ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j)) :
    ∀i j,i≠j → ((1-(s:ℝ))*ε)^2 ≤ square (mean (y i) u s-mean (y j) u s) := by
  unfold mean
  simpa only [sub_sub_cancel] using scaled_separated y u (a:=1-(s:ℝ)) (sub_nonneg.mpr s.property.2) hε hsep

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking
instance : MeasurableSpace C(Time,Point) := borel _
instance : BorelSpace C(Time,Point) := ⟨rfl⟩

def center (β : C(Time,ℝ)) : C(Time,ℝ) := β-β 0 • (1-linearPath)-β 1 • linearPath
@[fun_prop] lemma center_continuous : Continuous center := by unfold center; fun_prop
lemma center_zero (β : C(Time,ℝ)) : center β 0=0 := by simp [center,linearPath]
lemma center_one (β : C(Time,ℝ)) : center β 1=0 := by simp [center,linearPath]
lemma center_eq {β : C(Time,ℝ)} (h0 : β 0=0) (h1 : β 1=0) : center β=β := by simp [center,h0,h1]
def pinned (β : Noise) : Noise := fun j ↦ center (β j)
lemma pinned_continuous : Continuous pinned := continuous_pi (fun j ↦ center_continuous.comp (continuous_apply j))
lemma pinned_law : law.map pinned=law := by
  have h : pinned=ᵐ[law] id := by
    have hβ : ∀j : Fin 3,∀ᵐ β ∂law,(β j) 0=0 ∧ (β j) 1=0 := fun j ↦ by
      exact (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints
    filter_upwards [ae_all_iff.mpr hβ] with β hβ
    funext j
    exact center_eq (hβ j).1 (hβ j).2
  rw [Measure.map_congr h,Measure.map_id]

lemma pinned_leg_zero (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 0=y := by
  ext j
  simp [leg,mean,pinned,center_zero]
lemma pinned_leg_one (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 1=u := by
  ext j
  simp [leg,mean,pinned,center_one]

def leftTime (s : Time) : Time := ⟨min (2*(s:ℝ)) 1,by
  constructor
  · exact le_min (mul_nonneg (by norm_num) s.property.1) zero_le_one
  · exact min_le_right _ _⟩
def rightTime (s : Time) : Time := ⟨max (2*(s:ℝ)-1) 0,by
  constructor
  · exact le_max_right _ _
  · apply max_le ?_ zero_le_one
    linarith [s.property.2]⟩
@[fun_prop] lemma leftTime_continuous : Continuous leftTime := by unfold leftTime; fun_prop
@[fun_prop] lemma rightTime_continuous : Continuous rightTime := by unfold rightTime; fun_prop

def midpointTime : Time := ⟨1/2,by norm_num⟩

def trialPath (t : ℝ) (y z : Point) (u : Point) (β : Noise×Noise) : C(Time,Point) :=
  ⟨fun s ↦ leg t y u (pinned β.1) (leftTime s)+
    leg t z u (pinned β.2) (reverseTime (rightTime s))-u,by
    apply Continuous.sub _ continuous_const
    apply Continuous.add
    · exact (leg t y u (pinned β.1)).continuous.comp leftTime_continuous
    · exact (leg t z u (pinned β.2)).continuous.comp (reverseTime.continuous.comp rightTime_continuous)⟩

lemma trial_zero (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β 0=y := by
  have hl : leftTime 0=0 := by ext; simp [leftTime]
  have hr : reverseTime (rightTime 0)=1 := by ext; simp [rightTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_zero,pinned_leg_one,add_sub_cancel_right]
lemma trial_one (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β 1=z := by
  have hl : leftTime 1=1 := by ext; norm_num [leftTime]
  have hr : reverseTime (rightTime 1)=0 := by ext; norm_num [rightTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_zero,pinned_leg_one]
  abel
lemma trial_midpoint (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β midpointTime=u := by
  have hl : leftTime midpointTime=1 := by ext; norm_num [leftTime,midpointTime]
  have hr : reverseTime (rightTime midpointTime)=1 := by ext; norm_num [rightTime,midpointTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one,add_sub_cancel_right]

@[fun_prop] lemma trialPath_continuous (t : ℝ) (y z : Point) :
    Continuous (fun p : Point×(Noise×Noise) ↦ trialPath t y z p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (Point×(Noise×Noise))×Time ↦ fun j ↦
    (mean y p.1.1 (leftTime p.2) j+Real.sqrt (2*t)*center (p.1.2.1 j) (leftTime p.2))+
    (mean z p.1.1 (reverseTime (rightTime p.2)) j+Real.sqrt (2*t)*center (p.1.2.2 j) (reverseTime (rightTime p.2)))-p.1.1 j)
  unfold mean
  have hl := leftTime_continuous
  have hr := reverseTime.continuous.comp rightTime_continuous
  have hc := center_continuous
  fun_prop

def trialKernel (t : ℝ) (y z : Point) : Kernel Point C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod (Kernel.const Point (law.prod law))).map
    (fun p ↦ trialPath t y z p.1 p.2)
instance trialKernel_markov (t : ℝ) (y z : Point) : IsMarkovKernel (trialKernel t y z) := by
  unfold trialKernel
  exact Kernel.IsMarkovKernel.map _ (trialPath_continuous t y z).measurable

lemma trialKernel_apply (t : ℝ) (y z u : Point) : trialKernel t y z u=
    (law.prod law).map (trialPath t y z u) := by
  rw [trialKernel,Kernel.map_apply _ (trialPath_continuous t y z).measurable,Kernel.prod_apply,
    Kernel.deterministic_apply,Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map (trialPath_continuous t y z).measurable (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id u)))]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
