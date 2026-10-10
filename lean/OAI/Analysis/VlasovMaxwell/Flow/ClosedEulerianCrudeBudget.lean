import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.DyadicBalanceConstant
import OAI.Analysis.VlasovMaxwell.Geometry.PhysicalGeometryCutoffDensity

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_crude_budget {s : Solution} {T a b I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hI : b-a≤I) (hr : 0≤B.rmin) (hq : 0<B.qmin) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (I+B.rmax)/ENNReal.ofReal B.qmin*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  let c := max 0 (a-B.rmax)
  let d := min T (b-B.rmin)
  have hC : Icc c d⊆Icc 0 T := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hb := F.cone_occupation_energy_bound (p:=B.qmin) (a:=c) (b:=d) hT hs zX
    (F.measurable_closedBinEulerian hs hT zX B hS hJ hC) inter_subset_right hq.le
    (fun r z hz=>(F.closedBinEulerian_properties zX B S hC (r,z) hz).1)
    (fun r z hz=>(F.closedBinEulerian_properties zX B S hC (r,z) hz).2.1)
  have hw : d-c≤I+B.rmax := by
    dsimp [c,d]
    linarith [min_le_right T (b-B.rmin),le_max_right 0 (a-B.rmax)]
  have hb' := hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hw) le_rfl)
  have hh := mul_le_mul' (le_refl ((ENNReal.ofReal B.qmin)⁻¹)) hb'
  rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top,one_mul] at hh
  exact hh.trans_eq (by rw [div_eq_mul_inv]; ac_rfl)

lemma PhaseFlowOn.stable_jointBudget_entry {s : Solution} {T a b I r len : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (hI : 0<I) (hab : b-a≤I) (hr : r≤len) (hlen : len≤I) (n : ℕ×ℕ) :
    jointEnergyBudget s F.flow zX T 4 (max 0 (a-r-len)) (min T (b+len)) I n ≤
      ENNReal.ofReal (3468*(∫x : Vec,totalEnergy s (0,x))) := by
  have hmono := jointEnergyBudget_mono_interval (I:=I) s F.flow zX T 4 n
    (stable_source_enlargement (a:=a) (b:=b) (T:=T) hr hlen)
  refine hmono.trans ((ENNReal.le_tsum n).trans ?_)
  have hsum := F.stable_small_jointBudget_uniform hs zX hI hab
  apply hsum.trans_eq
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3468)]
  norm_num

lemma PhaseFlowOn.closedEulerian_baseline_budget {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len) (hlenI : len≤I) (hab : b-a≤I)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*
        ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x)) := by
  have hp0 : 0<p := by rw [hp]; positivity
  have hI : 0<I := hlen.trans_le hlenI
  have hq0 : 0<B.qmin := (div_pos hp0 (by norm_num)).trans_le hqmin
  by_cases hrad : B.rmax≤len
  · have ho := F.closedEulerian_stable_budget hs hT zX B hS np nf hp hφeq
      ha hb hlen hM hA hP hL hm hφ hφ1 hconst hstable hqmin hqmax hmq hmw
      hr hrmax hrad hd hDlo hDhi hw HX HZ hI
    have he := F.stable_jointBudget_entry hs zX hI hab hrad hlenI (np,nf)
    have hbound := ho.trans (mul_le_mul' le_rfl (add_le_add le_rfl
      (mul_le_mul' le_rfl he)))
    have heq : ENNReal.ofReal (40*B.rmax)/ENNReal.ofReal (p/256)*
        (ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal I/ENNReal.ofReal len*ENNReal.ofReal (3468*(∫x : Vec,totalEnergy s (0,x))))=
        ENNReal.ofReal ((40*B.rmax)/(p/256)*(1+(I/len)*3468))*
          ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3468)]
      rw [ENNReal.ofReal_mul (by positivity : 0≤(40*B.rmax)/(p/256)),
        ENNReal.ofReal_div_of_pos (by positivity : 0<p/256),
        ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_one,
        ENNReal.ofReal_mul (by positivity : 0≤I/len),ENNReal.ofReal_div_of_pos hlen]
      ring
    rw [heq] at hbound
    apply hbound.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have he : (40*B.rmax)/(p/256)*(1+I/len*3468)=
        10240*B.rmax/p*(1+I/len*3468) := by ring
    rw [he]
    have hh : 1+I/len*3468≤3468*(1+I/len) := by linarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)
  · have ho := F.closedEulerian_crude_budget hs hT zX B hS (Icc_subset_Icc ha hb) hab hr.le hq0
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq0]
    apply ENNReal.ofReal_le_ofReal
    have hlenr : len≤B.rmax := (lt_of_not_ge hrad).le
    have hn : 0≤I+B.rmax := by positivity
    calc
      (I+B.rmax)/B.qmin≤(I+B.rmax)/(p/128) :=
        div_le_div_of_nonneg_left hn (by positivity) hqmin
      _ ≤ (B.rmax*(1+I/len))/(p/128) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hi : I≤B.rmax*(I/len) := by
          have hh := mul_le_mul_of_nonneg_right hlenr (div_nonneg hI.le hlen.le)
          have he : len*(I/len)=I := by field_simp
          rwa [he] at hh
        nlinarith
      _ ≤ 35512320*B.rmax/p*(1+I/len) := by
        have he : (B.rmax*(1+I/len))/(p/128)=128*B.rmax/p*(1+I/len) := by ring
        rw [he]
        gcongr
        norm_num

lemma geometry_radial_balance {I R p θ φ H : ℝ}
    (hI : 0<I) (hR : 0<R) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hH : 0<H) :
    Summable (fun k : ℤ=>min (I*p^3*θ*φ^4*(H*(2:ℝ)^k))
      (R^2/(p*θ*(H*(2:ℝ)^k)))) ∧
    (∑'k : ℤ,min (I*p^3*θ*φ^4*(H*(2:ℝ)^k))
      (R^2/(p*θ*(H*(2:ℝ)^k)))) ≤ 6*Real.sqrt I*R*p*φ^2 := by
  let a := I*p^3*θ*φ^4*H
  let b := R^2/(p*θ*H)
  let r := R/(Real.sqrt I*p^2*θ*φ^2*H)
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have he (k : ℤ) : min (a*((2:ℝ)^k)^(1:ℝ)) (b*((2:ℝ)^k)^(-(1:ℝ)))=
      min (I*p^3*θ*φ^4*(H*(2:ℝ)^k)) (R^2/(p*θ*(H*(2:ℝ)^k))) := by
    rw [Real.rpow_one,Real.rpow_neg_one]
    dsimp [a,b]
    congr 1 <;> ring
  have hs := dyadic_power_min_summable ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  have ht := dyadic_balance_at ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1) hr
  simp_rw [he] at hs ht
  refine ⟨hs,ht.trans_eq ?_⟩
  norm_num only [Real.rpow_one,Real.rpow_neg_one]
  dsimp [a,b,r]
  have hsqrt : (Real.sqrt I)^2=I := Real.sq_sqrt hI.le
  have hs0 : Real.sqrt I≠0 := (Real.sqrt_pos.mpr hI).ne'
  field_simp
  nlinarith [hsqrt]

end RVM

end

end OAI
