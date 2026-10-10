import Mathlib
import OAI.Probability.SKFluctuations.ScalarVaryingFlattenedContinuity

namespace OAI

/-! Scalar Flatten Curvature. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.scalar_derivA (J : HeatJet 0) (x : ℝ) :
    HasDerivAt (fun y => J.A (fun _ => y)) (J.A₁ 0 (fun _ => x)) x := by
  have hh := J.derivA (0:Fin 1 → ℝ) (fun _ => 1) x
  have he (r : ℝ) : (0:Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by ext i; simp
  simpa only [he,Nat.reduceAdd,Fin.sum_univ_one,one_mul] using hh

theorem HeatJet.scalar_derivA₁ (J : HeatJet 0) (x : ℝ) :
    HasDerivAt (fun y => J.A₁ 0 (fun _ => y)) (J.A₂ 0 (fun _ => x)) x := by
  have hh := J.derivA₁ 0 (0:Fin 1 → ℝ) x
  have he (r : ℝ) : (0:Fin 1 → ℝ)+r • Pi.single 0 1 = fun _ => r := by
    ext i
    rw [Fin.eq_zero i]
    simp
  simpa only [he] using hh

 
theorem scalarTailJet_flatten_gradient_difference {T q r m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (x : ℝ) :
    ((scalarTailJet hT α r).evolve hm (T*r)).G 0 (fun _ => x)-
      ((scalarTailJet hT α q).evolve hm (T*q)).G 0 (fun _ => x) =
      T/2*(∫ s in q..r, (m-α.val s)*
        (((scalarTailJet hT α s).square).evolve hm (T*s)).A₁ 0 (fun _ => x)) := by
  let V := (scalarTailJetFamily hT α).square
  have hz : Continuous (fun p : ℝ × ℝ => (p.1,fun _ : Fin 1 => p.2)) := by fun_prop
  have hA := (V.evolve_A_continuous hm (c:=fun s => T*s) (continuous_const.mul continuous_id)).comp hz
  have hA₁ := (V.evolve_A₁_continuous hm (c:=fun s => T*s) (continuous_const.mul continuous_id) 0).comp hz
  have hd := (weighted_profile_integral_hasDerivAt hA hA₁
    (fun s y => ((V.J s).evolve hm (T*s)).scalar_derivA y) α m q r x).const_mul (T/2)
  have he : (fun y => T/2*(∫ s in q..r, (m-α.val s)*
      ((V.J s).evolve hm (T*s)).A (fun _ => y))) =
      fun y => ((scalarTailJet hT α r).evolve hm (T*r)).F (fun _ => y)-
        ((scalarTailJet hT α q).evolve hm (T*q)).F (fun _ => y) := by
    funext y
    exact (scalarTailJet_flatten_difference_source hT hq hqr hr α hm hm1 hc (fun _ => y)).symm
  dsimp only [Function.comp_apply] at hd
  rw [he] at hd
  exact (((scalarTailJet hT α r).evolve hm (T*r)).scalar_derivF x |>.sub
    (((scalarTailJet hT α q).evolve hm (T*q)).scalar_derivF x)).unique hd

 

theorem scalarTailJet_flatten_curvature_difference {T q r m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (x : ℝ) :
    ((scalarTailJet hT α r).evolve hm (T*r)).H 0 (fun _ => x)-
      ((scalarTailJet hT α q).evolve hm (T*q)).H 0 (fun _ => x) =
      T/2*(∫ s in q..r, (m-α.val s)*
        (((scalarTailJet hT α s).square).evolve hm (T*s)).A₂ 0 (fun _ => x)) := by
  let V := (scalarTailJetFamily hT α).square
  have hz : Continuous (fun p : ℝ × ℝ => (p.1,fun _ : Fin 1 => p.2)) := by fun_prop
  have hA₁ := (V.evolve_A₁_continuous hm (c:=fun s => T*s) (continuous_const.mul continuous_id) 0).comp hz
  have hA₂ := (V.evolve_A₂_continuous hm (c:=fun s => T*s) (continuous_const.mul continuous_id) 0).comp hz
  have hd := (weighted_profile_integral_hasDerivAt hA₁ hA₂
    (fun s y => ((V.J s).evolve hm (T*s)).scalar_derivA₁ y) α m q r x).const_mul (T/2)
  have he : (fun y => T/2*(∫ s in q..r, (m-α.val s)*
      ((V.J s).evolve hm (T*s)).A₁ 0 (fun _ => y))) =
      fun y => ((scalarTailJet hT α r).evolve hm (T*r)).G 0 (fun _ => y)-
        ((scalarTailJet hT α q).evolve hm (T*q)).G 0 (fun _ => y) := by
    funext y
    exact (scalarTailJet_flatten_gradient_difference hT hq hqr hr α hm hm1 hc y).symm
  dsimp only [Function.comp_apply] at hd
  rw [he] at hd
  exact (((scalarTailJet hT α r).evolve hm (T*r)).scalar_derivG x |>.sub
    (((scalarTailJet hT α q).evolve hm (T*q)).scalar_derivG x)).unique hd

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarTailJet_flatten_curvature_hasDerivWithinAt {T q m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hq1 : q < 1) (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (x : ℝ) :
    HasDerivWithinAt
      (fun r => ((scalarTailJet hT α r).evolve hm (T*r)).H 0 (fun _ => x))
      (T/2*((m-α.val q)*(((scalarTailJet hT α q).square).evolve hm (T*q)).A₂ 0 (fun _ => x)))
      (Ici q) q := by
  let V := (scalarTailJetFamily hT α).square
  let B : ℝ → ℝ := fun s => ((V.J s).evolve hm (T*s)).A₂ 0 (fun _ => x)
  have hV := V.evolve_A₂_continuous hm (c:=fun s => T*s)
    (continuous_const.mul continuous_id) 0
  have hz : Continuous (fun s : ℝ => (s,(fun _ : Fin 1 => x))) :=
    continuous_id.prodMk continuous_const
  have hB : Continuous B := by
    simpa only [Function.comp_def,B] using hV.comp hz
  have hi : IntervalIntegrable (fun s => (m-α.val s)*B s) volume 0 q :=
    (intervalIntegrable_const.sub α.property.2.intervalIntegrable).mul_continuousOn hB.continuousOn
  have hd0 : HasDerivWithinAt (fun r => ∫ s in (0:ℝ)..r, (m-α.val s)*B s)
      ((m-α.val q)*B q) (Ici q) q := intervalIntegral.integral_hasDerivWithinAt_right hi
    ((measurable_const.sub α.property.2.measurable).mul hB.measurable).stronglyMeasurable.stronglyMeasurableAtFilter
    (((hc q).mono Ioi_subset_Ici_self).const_sub m |>.mul hB.continuousWithinAt)
  have hd := hd0.const_mul (T/2)
  have hd' := hd.const_add (((scalarTailJet hT α 0).evolve hm (T*0)).H 0 (fun _ => x))
  apply hd'.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[≥] q, r < 1 from
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq1))] with r hr hr1
    have he := scalarTailJet_flatten_curvature_difference hT (q:=0) le_rfl
      (hq.trans hr) hr1.le α hm hm1 hc x
    change _-_ = T/2*(∫ s in (0:ℝ)..r, (m-α.val s)*B s) at he
    linarith
  · have he := scalarTailJet_flatten_curvature_difference hT (q:=0) le_rfl
      hq hq1.le α hm hm1 hc x
    change _-_ = T/2*(∫ s in (0:ℝ)..q, (m-α.val s)*B s) at he
    linarith

 

theorem scalarTailJet_origin_flatten_curvature_stationary {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hm : 0 < α.val 0)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (x : ℝ) :
    HasDerivWithinAt
      (fun q => ((scalarTailJet hT α q).evolve hm (T*q)).H 0 (fun _ => x)) 0 (Ici 0) 0 := by
  simpa only [sub_self,zero_mul,mul_zero] using
    scalarTailJet_flatten_curvature_hasDerivWithinAt hT (q:=0) le_rfl zero_lt_one α hm
      (α.property.1 0).2 hc x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem right_deriv_mul_continuous {C : ℝ → ℝ}
    (hc : ContinuousWithinAt C (Ioi 0) 0) :
    HasDerivWithinAt (fun q => q*C q) (C 0) (Ioi 0) 0 := by
  apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [slope_def_field,zero_mul,sub_zero]
  exact (mul_div_cancel_left₀ _ (ne_of_gt (show 0 < q from hq))).symm

 

theorem scalarTailJet_origin_curvature_hasDerivWithinAt {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hm : 0 < α.val 0)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) :
    HasDerivWithinAt (fun q => (scalarTailJet hT α q).H 0 0)
      (-(T/2)*(scalarTailSpatialJet hT α 4 0 0+
        2*α.val 0*((scalarTailJet hT α 0).H 0 0)^2)) (Ioi 0) 0 := by
  let C : ℝ → ℝ := fun q => T*scalarTailCurvatureRate hT α q (α.val 0) (T*q)
  have hC : Continuous C := by
    have hz : Continuous (fun q : ℝ => (T*q,(q,α.val 0))) := by fun_prop
    exact ((scalarTailCurvatureRate_continuous hT α).comp hz).const_mul T
  have hd := (scalarTailJet_origin_flatten_curvature_stationary hT α hm hc 0).mono Ioi_subset_Ici_self
  have he := hd.sub (right_deriv_mul_continuous hC.continuousWithinAt)
  have hd' : -(T/2)*(scalarTailSpatialJet hT α 4 0 0+
      2*α.val 0*((scalarTailJet hT α 0).H 0 0)^2) = 0-C 0 := by
    dsimp only [C]
    rw [mul_zero,scalarTailCurvatureRate_zero,unitMassClip_eq (α.property.1 0)]
    ring
  rw [hd']
  apply he.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : 0 ≤ T*q := mul_nonneg hT.le hq.le
    have hx := scalarTailCurvatureRate_eq hT α (q:=q) hm (α.property.1 0).2 hq0
    change (scalarTailJet hT α q).H 0 0 =
      ((scalarTailJet hT α q).evolve hm (T*q)).H 0 0-q*C q
    dsimp only [C]
    rw [hx]
    ring
  · change (scalarTailJet hT α 0).H 0 0 =
      ((scalarTailJet hT α 0).evolve hm (T*0)).H 0 0-0*C 0
    simp only [zero_mul,sub_zero,mul_zero]
    have hx := scalarTailCurvatureRate_eq hT α (q:=0) hm (α.property.1 0).2 (t:=0) le_rfl
    simpa only [zero_mul,add_zero] using hx.symm

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def rightSlope (f : ℝ → ℝ) (d q : ℝ) : ℝ :=
  if q = 0 then d else (f q-f 0)/q

theorem rightSlope_continuousWithinAt {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt f d (Ioi 0) 0) :
    ContinuousWithinAt (rightSlope f d) (Ioi 0) 0 := by
  have hh := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hd
  change Tendsto (rightSlope f d) (𝓝[Ioi 0] 0) (𝓝 (rightSlope f d 0))
  simp only [rightSlope,ite_true]
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : q ≠ 0 := ne_of_gt (show 0 < q from hq)
  simp only [rightSlope,hq',ite_false,slope_def_field,sub_zero]

theorem exists_small_upper_triangle_within {R : ℝ × ℝ → ℝ} {a : ℝ → ℝ}
    (hcR : ContinuousWithinAt R (Ioi 0 ×ˢ (univ : Set ℝ)) (0,a 0))
    (hc : ContinuousWithinAt a (Ici 0) 0) (hR : R (0,a 0) < 0) :
    ∃ q ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) q, R (s,a q) < 0 := by
  obtain ⟨δ,hδ,hδR⟩ := Metric.continuousWithinAt_iff.mp hcR (-R (0,a 0)) (by linarith)
  obtain ⟨ε,hε,hεa⟩ := Metric.continuousWithinAt_iff.mp hc δ hδ
  let q := min 1 (min δ ε)/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [min_le_left (1:ℝ) (min δ ε)]
  have hqd : q < δ := by dsimp [q]; linarith [min_le_right (1:ℝ) (min δ ε),min_le_left δ ε]
  have hqe : q < ε := by dsimp [q]; linarith [min_le_right (1:ℝ) (min δ ε),min_le_right δ ε]
  have haq : dist (a q) (a 0) < δ := hεa hq.le
    (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hq] using hqe)
  refine ⟨q,⟨hq,hq1⟩,?_⟩
  intro s hs
  have hh := hδR (show (s,a q) ∈ Ioi 0 ×ˢ (univ : Set ℝ) from ⟨hs.1,mem_univ _⟩)
    (show dist (s,a q) (0,a 0) < δ from by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs.1] using hs.2.trans hqd,haq⟩)
  rw [Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).2]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def scalarTailSecondRate {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m t : ℝ) : ℝ :=
  let J := scalarTailJet hT α q
  let H := scalarTailTestJet hT α 1 q
  let U := scalarTailTestJet hT α 2 q
  let a := unitMassClip m
  H.square.testAverageRate a t 0+(J.testProduct U).testAverageRate a t 0+
    (5*a/2)*(J.square.testProduct H).testAverageRate a t 0+
    (a^2/2)*J.square.square.testAverageRate a t 0-
    (a/2)*J.square.testAverageRate a t 0*(J.H 0 0+t*H.testAverageRate a t 0)-
    (a^2/2)*t*(J.square.testAverageRate a t 0)^2

theorem scalarTailSecondRate_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => scalarTailSecondRate hT α p.2.1 p.2.2 p.1) := by
  let V := scalarTailJetFamily hT α
  let H := scalarTailTestFamily hT α 1
  let U := scalarTailTestFamily hT α 2
  have h0 := H.square.testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have h1 := (V.testProduct U).testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have h2 := (V.square.testProduct H).testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have h3 := V.square.square.testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hQ := V.square.testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hH := H.testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hz : Continuous (fun p : ℝ × (ℝ × ℝ) => (p.2.1,(0:Fin 1 → ℝ))) := by fun_prop
  have hHC := (V.continuousH 0).comp hz
  have hm := unitMassClip_continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2))
  exact (((((h0.add h1).add (((hm.const_mul 5).div_const 2).mul h2)).add
    (((hm.pow 2).div_const 2).mul h3)).sub
      (((hm.div_const 2).mul hQ).mul (hHC.add (continuous_fst.mul hH)))).sub
        ((((hm.pow 2).div_const 2).mul continuous_fst).mul (hQ.pow 2)))

theorem scalarTailSpatialJet_three_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    scalarTailSpatialJet hT α 3 q 0 = 0 := by
  have hh := scalarProfileJet_parity (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) 3 0
  norm_num only [neg_zero,show (-1:ℝ)^3 = -1 by norm_num] at hh
  change scalarTailSpatialJet hT α 3 q 0 = -1*scalarTailSpatialJet hT α 3 q 0 at hh
  linarith

theorem scalarTailSecondRate_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q m : ℝ) :
    scalarTailSecondRate hT α q m 0 =
      2*((scalarTailJet hT α q).H 0 0*scalarTailSpatialJet hT α 4 q 0)+
        2*unitMassClip m*((scalarTailJet hT α q).H 0 0)^3 := by
  have h0 := scalarTailJet_A_zero hT α q
  have h3 := scalarTailSpatialJet_three_zero hT α q
  unfold scalarTailSecondRate
  simp only [HeatJet.testAverageRate_zero_scalar]
  simp only [HeatJet.square,HeatJet.testProduct,scalarTailTestJet]
  change (scalarTailSpatialJet hT α 1 q 0) = 0 at h0
  simp only [Nat.reduceAdd, show (scalarTailJet hT α q).A 0 = scalarTailSpatialJet hT α 1 q 0 from rfl,
    show (scalarTailJet hT α q).G 0 0 = scalarTailSpatialJet hT α 1 q 0 from rfl,
    show (scalarTailJet hT α q).A₁ 0 0 = scalarTailSpatialJet hT α 2 q 0 from rfl,
    show (scalarTailJet hT α q).A₂ 0 0 = scalarTailSpatialJet hT α 3 q 0 from rfl,
    show (scalarTailJet hT α q).H 0 0 = scalarTailSpatialJet hT α 2 q 0 from rfl,h0,h3]
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTail_observedRate_trace {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m t : ℝ) :
    (scalarTailJet hT α q).observedRate m t 0 =
      let J := scalarTailJet hT α q
      let H := scalarTailTestJet hT α 1 q
      let U := scalarTailTestJet hT α 2 q
      clockTest m J.F H.square.A t 0+clockTest m J.F (J.testProduct U).A t 0+
        (5*m/2)*clockTest m J.F (J.square.testProduct H).A t 0+
        (m^2/2)*clockTest m J.F J.square.square.A t 0-
        (m/2)*clockTest m J.F J.square.A t 0*clockTest m J.F H.A t 0-
        (m^2/2)*(clockTest m J.F J.square.A t 0)^2 := by
  let J := scalarTailJet hT α q
  let H := scalarTailTestJet hT α 1 q
  let U := scalarTailTestJet hT α 2 q
  have htr : testedHeatTrace m J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ =
      fun y => 2*H.square.A y+2*(J.testProduct U).A y+
        (5*m)*(J.square.testProduct H).A y+m^2*J.square.square.A y := by
    funext y
    simp only [testedHeatTrace,HeatJet.square,HeatJet.testProduct,Nat.reduceAdd,Fin.sum_univ_one]
    change 2*((J.H 0 y)^2+J.A y*J.A₂ 0 y)+2*m*(2*(J.A y*J.H 0 y))*J.A y+
      J.A y^2*(m*J.H 0 y+m^2*J.A y^2) = _
    change _ = 2*(J.H 0 y)^2+2*(J.A y*J.A₂ 0 y)+(5*m)*(J.A y^2*J.H 0 y)+m^2*(J.A y^2)^2
    ring
  have hpr : potentialHeatTrace m J.square.G J.square.H =
      fun y => m*H.A y+m^2*J.square.A y := by
    funext y
    simp only [potentialHeatTrace,HeatJet.square,Nat.reduceAdd,Fin.sum_univ_one]
    rfl
  change (1/2:ℝ)*(clockTest m J.F (testedHeatTrace m J.square.G J.square.H J.square.A
      J.square.A₁ J.square.A₂) t 0-clockTest m J.F J.square.A t 0*
      clockTest m J.F (potentialHeatTrace m J.square.G J.square.H) t 0) = _
  rw [htr,hpr]
  rw [clockTest_add_test J.lipschitz
      (((H.square.smoothA.const_mul 2).add ((J.testProduct U).smoothA.const_mul 2)).add
        ((J.square.testProduct H).smoothA.const_mul (5*m)))
      (J.square.square.smoothA.const_mul (m^2)),
    clockTest_add_test J.lipschitz
      ((H.square.smoothA.const_mul 2).add ((J.testProduct U).smoothA.const_mul 2))
      ((J.square.testProduct H).smoothA.const_mul (5*m)),
    clockTest_add_test J.lipschitz (H.square.smoothA.const_mul 2) ((J.testProduct U).smoothA.const_mul 2),
    clockTest_add_test J.lipschitz (H.smoothA.const_mul m) (J.square.smoothA.const_mul (m^2))]
  simp only [clockTest_const_mul]
  ring

theorem scalarTailSecondRate_eq {T q m t : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (hm : m ∈ Icc (0:ℝ) 1) (ht : 0 ≤ t) :
    (scalarTailJet hT α q).observedRate m t 0 = ((scalarTailJet hT α q).H 0 0)^2+
      t*scalarTailSecondRate hT α q m t := by
  let J := scalarTailJet hT α q
  let H := scalarTailTestJet hT α 1 q
  let U := scalarTailTestJet hT α 2 q
  have h0 : J.A 0 = 0 := scalarTailJet_A_zero hT α q
  have hh := H.square.testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  have hu := (J.testProduct U).testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  have hsh := (J.square.testProduct H).testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  have hss := J.square.square.testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  have hs := J.square.testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  have hc := H.testAverageRate_eq m ht (0 : Fin 1 → ℝ)
  change clockTest m J.F H.square.A t 0 = (J.H 0 0)^2+t*_ at hh
  change clockTest m J.F (J.testProduct U).A t 0 = J.A 0*U.A 0+t*_ at hu
  change clockTest m J.F (J.square.testProduct H).A t 0 = (J.A 0)^2*H.A 0+t*_ at hsh
  change clockTest m J.F J.square.square.A t 0 = ((J.A 0)^2)^2+t*_ at hss
  change clockTest m J.F J.square.A t 0 = (J.A 0)^2+t*_ at hs
  change clockTest m J.F H.A t 0 = J.H 0 0+t*_ at hc
  rw [scalarTail_observedRate_trace]
  dsimp only
  change clockTest m J.F H.square.A t 0+clockTest m J.F (J.testProduct U).A t 0+
        (5*m/2)*clockTest m J.F (J.square.testProduct H).A t 0+
        (m^2/2)*clockTest m J.F J.square.square.A t 0-
        (m/2)*clockTest m J.F J.square.A t 0*clockTest m J.F H.A t 0-
        (m^2/2)*(clockTest m J.F J.square.A t 0)^2 = _
  rw [hh,hu,hsh,hss,hs,hc,h0]
  unfold scalarTailSecondRate
  rw [unitMassClip_eq hm]
  change _ = (J.H 0 0)^2+t*(H.square.testAverageRate m t 0+(J.testProduct U).testAverageRate m t 0+
    (5*m/2)*(J.square.testProduct H).testAverageRate m t 0+
    (m^2/2)*J.square.square.testAverageRate m t 0-
    (m/2)*J.square.testAverageRate m t 0*(J.H 0 0+t*H.testAverageRate m t 0)-
    (m^2/2)*t*(J.square.testAverageRate m t 0)^2)
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

noncomputable def scalarHeadSecondRate {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m : ℝ) : ℝ :=
  T^2*∫ u in (0:ℝ)..1, u*scalarTailSecondRate hT α q m (T*q*u)

theorem scalarHeadSecondRate_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × ℝ => scalarHeadSecondRate hT α p.1 p.2) := by
  have hh := scalarTailSecondRate_continuous hT α
  have hz : Continuous (fun p : (ℝ × ℝ) × ℝ => (T*p.1.1*p.2,p.1)) := by fun_prop
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      p.2*scalarTailSecondRate hT α p.1.1 p.1.2 (T*p.1.1*p.2)) :=
    Continuous.mul (f:=fun p : (ℝ × ℝ) × ℝ => p.2)
      (g:=fun p => scalarTailSecondRate hT α p.1.1 p.1.2 (T*p.1.1*p.2))
      continuous_snd (Continuous.comp
        (g:=fun p : ℝ × (ℝ × ℝ) => scalarTailSecondRate hT α p.2.1 p.2.2 p.1)
        (f:=fun p : (ℝ × ℝ) × ℝ => (T*p.1.1*p.2,p.1)) hh hz)
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1).const_mul (T^2)

theorem scalarHeadSecondRate_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (m : ℝ) :
    scalarHeadSecondRate hT α 0 m = T^2*
      ((scalarTailJet hT α 0).H 0 0*scalarTailSpatialJet hT α 4 0 0+
        unitMassClip m*((scalarTailJet hT α 0).H 0 0)^3) := by
  unfold scalarHeadSecondRate
  simp only [mul_zero,zero_mul,scalarTailSecondRate_zero]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_id]
  norm_num only [one_pow,zero_pow (by omega : 2 ≠ 0),sub_zero]
  ring

theorem scalarHeadObservedRatio_second_expansion {T q m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hm : m ∈ Icc (0:ℝ) 1) :
    scalarHeadObservedRatio hT α q m = T*((scalarTailJet hT α q).H 0 0)^2+
      q*scalarHeadSecondRate hT α q m := by
  have hz : Continuous (fun u : ℝ => (T*q*u,(q,m))) := by fun_prop
  have hS : Continuous (fun u : ℝ => u*scalarTailSecondRate hT α q m (T*q*u)) :=
    Continuous.mul (f:=fun u : ℝ => u)
      (g:=fun u => scalarTailSecondRate hT α q m (T*q*u))
      continuous_id (Continuous.comp
        (g:=fun p : ℝ × (ℝ × ℝ) => scalarTailSecondRate hT α p.2.1 p.2.2 p.1)
        (f:=fun u : ℝ => (T*q*u,(q,m))) (scalarTailSecondRate_continuous hT α) hz)
  unfold scalarHeadObservedRatio
  rw [unitMassClip_eq hm]
  have he : (∫ u in (0:ℝ)..1, (scalarTailJet hT α q).observedRate m (T*q*u) 0) =
      ∫ u in (0:ℝ)..1, ((scalarTailJet hT α q).H 0 0)^2+
        (T*q)*(u*scalarTailSecondRate hT α q m (T*q*u)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro u hu
    dsimp only
    rw [scalarTailSecondRate_eq hT α hm (mul_nonneg (mul_nonneg hT.le hq) hu.1.le)]
    ring
  rw [he,intervalIntegral.integral_add intervalIntegrable_const
    ((hS.const_mul (T*q)).intervalIntegrable (μ:=volume) 0 1),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
  simp only [sub_zero,one_smul]
  unfold scalarHeadSecondRate
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem exists_small_upper_triangle {R : ℝ × ℝ → ℝ} {a : ℝ → ℝ}
    (hcR : Continuous R) (hc : ContinuousWithinAt a (Ici 0) 0)
    (hR : R (0,a 0) < 1) :
    ∃ q ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) q, R (s,a q) < 1 := by
  have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,a 0), R p < 1 :=
    hcR.continuousAt.eventually (eventually_lt_nhds hR)
  obtain ⟨δ,hδ,hδR⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨ε,hε,hεa⟩ := Metric.continuousWithinAt_iff.mp hc δ hδ
  let q := min 1 (min δ ε)/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [min_le_left (1:ℝ) (min δ ε)]
  have hqd : q < δ := by dsimp [q]; linarith [min_le_right (1:ℝ) (min δ ε),min_le_left δ ε]
  have hqe : q < ε := by dsimp [q]; linarith [min_le_right (1:ℝ) (min δ ε),min_le_right δ ε]
  have haq : dist (a q) (a 0) < δ := hεa hq.le
    (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hq] using hqe)
  refine ⟨q,⟨hq,hq1⟩,?_⟩
  intro s hs
  apply hδR
  rw [Prod.dist_eq,max_lt_iff]
  exact ⟨by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs.1] using hs.2.trans hqd,haq⟩

theorem exists_small_right_interval {f : ℝ → ℝ} (hc : Continuous f) (hf : 1 < f 0) :
    ∃ q ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) q, 1 < f s := by
  have he : ∀ᶠ s in 𝓝 (0:ℝ), 1 < f s := hc.continuousAt.eventually (eventually_gt_nhds hf)
  obtain ⟨δ,hδ,hδR⟩ := Metric.eventually_nhds_iff.mp he
  let q := min 1 δ/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [min_le_left (1:ℝ) δ]
  have hqd : q < δ := by dsimp [q]; linarith [min_le_right (1:ℝ) δ]
  refine ⟨q,⟨hq,hq1⟩,?_⟩
  intro s hs
  exact hδR (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs.1] using hs.2.trans hqd)

theorem scalarMinimizer_upper_head_obstruction {T q : ℝ} (hT : 1 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β)
    (hR : ∀ s ∈ Ioo (0:ℝ) q, scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val q) < 1) :
    False := by
  have hm := scalarMinimizer_strict_origin hT α hα hmin hq.1
  have hm0 : 0 < α.val q := (α.property.1 0).1.trans_lt hm
  have hv := scalarMinimizer_head_variation (zero_lt_one.trans hT) hq α hα hm0
    (α.property.1 q).2 le_rfl hc hmin
  let f : ℝ → ℝ := fun s => (α.val q-α.val s)*s*
    (1-scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val q))
  have hi : IntervalIntegrable f volume 0 q := by
    convert (scalarHeadVariation_integrable (zero_lt_one.trans hT) α (α.val q) 0 q).neg using 1
    funext s
    dsimp [f]
    ring
  obtain ⟨δ,hδ,hδa⟩ := Metric.continuousWithinAt_iff.mp (hc 0) (α.val q-α.val 0) (sub_pos.mpr hm)
  have hq0 := hq.1
  let u := min q δ/2
  have hu : 0 < u := by dsimp [u]; positivity
  have huq : u ≤ q := by dsimp [u]; linarith [min_le_left q δ]
  have hud : u < δ := by dsimp [u]; linarith [min_le_right q δ]
  have hp : 0 < ∫ s in (0:ℝ)..q, f s := by
    apply integral_pos_of_initial_pos hu huq hi
    · intro s hs
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr (α.property.2 hs.2.le)) hs.1.le)
        (sub_nonneg.mpr (hR s hs).le)
    · intro s hs
      have hd := hδa hs.1.le (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs.1] using hs.2.trans hud)
      rw [Real.dist_eq] at hd
      have ham : α.val s < α.val q := by linarith [(abs_lt.mp hd).2]
      exact mul_pos (mul_pos (sub_pos.mpr ham) hs.1) (sub_pos.mpr (hR s ⟨hs.1,hs.2.trans_le huq⟩))
  have he : (fun s => (α.val q-α.val s)*s*
      (scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val q)-1)) = fun s => -f s := by
    funext s
    dsimp [f]
    ring
  rw [he,intervalIntegral.integral_neg] at hv
  linarith

 

theorem scalarMinimizer_origin_curvature_ge {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    1 ≤ T*((scalarTailJet (zero_lt_one.trans hT) α 0).A₁ 0 0)^2 := by
  by_contra hn
  have hR : scalarHeadObservedRatio (zero_lt_one.trans hT) α 0 (α.val 0) < 1 := by
    rw [scalarHeadObservedRatio_zero]
    exact lt_of_not_ge hn
  obtain ⟨q,hq,hqR⟩ := exists_small_upper_triangle
    (scalarHeadObservedRatio_continuous (zero_lt_one.trans hT) α) (hc 0) hR
  exact scalarMinimizer_upper_head_obstruction hT hq α hα hc hmin hqR

theorem scalarMinimizer_lower_head_obstruction {T q : ℝ} (hT : 1 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (hm : 0 < α.val 0)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β)
    (hR : ∀ s ∈ Ioo (0:ℝ) q, 1 < scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val 0)) :
    False := by
  have hv := scalarMinimizer_head_variation (zero_lt_one.trans hT) hq α hα hm
    (α.property.1 0).2 (α.property.2 hq.1.le) hc hmin
  let f : ℝ → ℝ := fun s => (α.val s-α.val 0)*s*
    (scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val 0)-1)
  have hi : IntervalIntegrable f volume 0 q := by
    convert (scalarHeadVariation_integrable (zero_lt_one.trans hT) α (α.val 0) 0 q).neg using 1
    funext s
    dsimp [f]
    ring
  have hp : 0 < ∫ s in (0:ℝ)..q, f s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hi (fun s hs =>
      mul_pos (mul_pos (sub_pos.mpr (scalarMinimizer_strict_origin hT α hα hmin hs.1)) hs.1)
        (sub_pos.mpr (hR s hs))) hq.1
  have he : (fun s => (α.val 0-α.val s)*s*
      (scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val 0)-1)) = fun s => -f s := by
    funext s
    dsimp [f]
    ring
  rw [he,intervalIntegral.integral_neg] at hv
  linarith

 

theorem scalarMinimizer_origin_atom_marginality {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (hm : 0 < α.val 0)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    T*((scalarTailJet (zero_lt_one.trans hT) α 0).A₁ 0 0)^2 = 1 := by
  apply le_antisymm _ (scalarMinimizer_origin_curvature_ge hT α hα hc hmin)
  by_contra hn
  have hR : 1 < scalarHeadObservedRatio (zero_lt_one.trans hT) α 0 (α.val 0) := by
    rw [scalarHeadObservedRatio_zero]
    exact lt_of_not_ge hn
  have hcR : Continuous (fun s => scalarHeadObservedRatio (zero_lt_one.trans hT) α s (α.val 0)) :=
    (scalarHeadObservedRatio_continuous (zero_lt_one.trans hT) α).comp
      (f := fun s : ℝ => (s,α.val 0)) (continuous_id.prodMk continuous_const)
  obtain ⟨q,hq,hqR⟩ := exists_small_right_interval hcR hR
  exact scalarMinimizer_lower_head_obstruction hT hq α hα hc hm hmin hqR

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem weighted_head_integral_continuousOn {R : ℝ × ℝ → ℝ} (hR : Continuous R)
    (α : boundedMassProfiles) {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (fun m => ∫ s in (0:ℝ)..q, (m-α.val s)*s*(R (s,m)-1)) (Icc (0:ℝ) 1) := by
  have hS : IsCompact (Icc (0:ℝ) q ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨K,hK⟩ := hS.bddAbove_image (hR.sub continuous_const).norm.continuousOn
  have hK' (s m : ℝ) (hs : s ∈ Icc (0:ℝ) q) (hm : m ∈ Icc (0:ℝ) 1) :
      |R (s,m)-1| ≤ K := hK ⟨(s,m),⟨hs,hm⟩,rfl⟩
  intro m₀ _
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound:=fun _ => q*K)
  · exact Eventually.of_forall fun m =>
      ((((measurable_const.sub α.property.2.measurable).mul measurable_id).mul
        ((hR.comp (continuous_id.prodMk continuous_const)).sub continuous_const).measurable
        ).stronglyMeasurable.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with m hm
    exact ae_of_all volume fun s hs => by
      rw [uIoc_of_le hq] at hs
      have hαs := α.property.1 s
      have hd : |m-α.val s| ≤ 1 := abs_le.mpr ⟨by linarith [hm.1,hm.2,hαs.1,hαs.2],by linarith [hm.1,hm.2,hαs.1,hαs.2]⟩
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos hs.1]
      calc
        |m-α.val s| *s*|R (s,m)-1| ≤ (1*q)*K :=
          mul_le_mul (mul_le_mul hd hs.2 hs.1.le zero_le_one) (hK' s m ⟨hs.1.le,hs.2⟩ hm)
            (abs_nonneg _) (by positivity)
        _ = q*K := by ring
  · exact intervalIntegrable_const
  · exact ae_of_all volume fun s _ =>
      (((continuous_id.sub continuous_const).mul continuous_const).mul
        ((hR.comp (continuous_const.prodMk continuous_id)).sub continuous_const)).continuousWithinAt

 

theorem scalarMinimizer_zero_head_variation {T q : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (haq : 0 < α.val q) (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    0 ≤ ∫ s in (0:ℝ)..q, -α.val s*s*(scalarHeadObservedRatio hT α s 0-1) := by
  have ht := weighted_head_integral_continuousOn (scalarHeadObservedRatio_continuous hT α)
    α hq.1.le 0 (show (0:ℝ) ∈ Icc 0 1 by simp)
  rw [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE zero_lt_one] at ht
  have ht' := ht.mono_left (nhdsWithin_mono (0:ℝ) Ioi_subset_Ici_self)
  simp only [zero_sub] at ht'
  apply ge_of_tendsto ht'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ m : ℝ in 𝓝[>] 0, m < α.val q from
      (eventually_lt_nhds haq).filter_mono nhdsWithin_le_nhds),
    (show ∀ᶠ m : ℝ in 𝓝[>] 0, m < 1 from
      (eventually_lt_nhds (zero_lt_one : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds)] with m hm hma hm1
  exact scalarMinimizer_head_variation hT hq α hα hm hm1.le hma.le hc hmin

end SKFluctuations.Hierarchy

end

end OAI
