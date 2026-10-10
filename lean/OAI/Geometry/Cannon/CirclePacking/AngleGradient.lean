import Mathlib

namespace OAI

/-! The variational angle functional for a conformal circle packing. -/

section
section
section
section
namespace CannonPackingGeometry
open Set Filter Topology MeasureTheory

noncomputable section

def angleGradient (θ : ℝ) : ℝ := Real.log (Real.sin (θ/2)) - Real.log (Real.cos (θ/2))

def angleEntropy (θ : ℝ) : ℝ :=
  2 * ((∫ x in (0:ℝ)..θ/2, Real.log (Real.sin x)) -
    (∫ x in (0:ℝ)..θ/2, Real.log (Real.cos x)))

lemma angleEntropy_continuous : Continuous angleEntropy := by
  have hs : Continuous (fun θ : ℝ => ∫ x in (0:ℝ)..θ, Real.log (Real.sin x)) :=
    intervalIntegral.continuous_primitive (fun _ _ => intervalIntegrable_log_sin) 0
  have hc : Continuous (fun θ : ℝ => ∫ x in (0:ℝ)..θ, Real.log (Real.cos x)) :=
    intervalIntegral.continuous_primitive (fun _ _ => intervalIntegrable_log_cos) 0
  exact continuous_const.mul ((hs.comp (by fun_prop)).sub (hc.comp (by fun_prop)))

lemma half_trig_pos {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    0 < Real.sin (θ/2) ∧ 0 < Real.cos (θ/2) := by
  rcases hθ with ⟨hθ0,hθπ⟩
  exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩⟩

lemma angleGradient_continuousAt {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    ContinuousAt angleGradient θ := by
  have hh := half_trig_pos hθ
  unfold angleGradient
  apply ContinuousAt.sub
  · apply ContinuousAt.log
    · exact (Real.continuous_sin.comp (continuous_id.div_const 2)).continuousAt
    · exact hh.1.ne'
  · apply ContinuousAt.log
    · exact (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt
    · exact hh.2.ne'

lemma angleEntropy_hasDerivAt {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    HasDerivAt angleEntropy (angleGradient θ) θ := by
  have hh := half_trig_pos hθ
  have hs := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun x => Real.log (Real.sin x)) volume 0 (θ/2) from intervalIntegrable_log_sin)
    ((Real.measurable_log.comp Real.continuous_sin.measurable).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((Real.continuousAt_log hh.1.ne').comp Real.continuous_sin.continuousAt)
  have hc := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun x => Real.log (Real.cos x)) volume 0 (θ/2) from intervalIntegrable_log_cos)
    ((Real.measurable_log.comp Real.continuous_cos.measurable).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((Real.continuousAt_log hh.2.ne').comp Real.continuous_cos.continuousAt)
  have hd := ((hs.comp θ ((hasDerivAt_id θ).div_const 2)).sub
    (hc.comp θ ((hasDerivAt_id θ).div_const 2))).const_mul 2
  have heq : 2 * (Real.log (Real.sin (θ/2))*(1/2) - Real.log (Real.cos (θ/2))*(1/2)) = angleGradient θ := by
    unfold angleGradient
    ring
  rw [heq] at hd
  exact hd

lemma angleGradient_zero_limit : Tendsto angleGradient (𝓝[>] (0:ℝ)) atBot := by
  have hs : Tendsto (fun θ : ℝ => Real.sin (θ/2)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show Continuous (fun θ : ℝ => Real.sin (θ/2)) by fun_prop).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi from Real.pi_pos)] with θ hθ
      exact (half_trig_pos hθ).1
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hs
  have hc : Tendsto (fun θ : ℝ => -Real.log (Real.cos (θ/2))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh : ContinuousAt (fun θ : ℝ => -Real.log (Real.cos (θ/2))) 0 := by
      apply ContinuousAt.neg
      apply ContinuousAt.log
      · fun_prop
      · norm_num
    simpa using hh.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  change Tendsto (fun x : ℝ => Real.log (Real.sin (x/2)) - Real.log (Real.cos (x/2))) _ _
  simpa only [sub_eq_add_neg,Function.comp_def] using hlog.atBot_add hc

lemma angleGradient_pi_sub (θ : ℝ) : angleGradient (Real.pi-θ) = -angleGradient θ := by
  unfold angleGradient
  have heq : (Real.pi-θ)/2=Real.pi/2-θ/2 := by ring
  rw [heq,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  ring

lemma angleGradient_pi_limit : Tendsto angleGradient (𝓝[<] Real.pi) atTop := by
  have ht : Tendsto (fun θ : ℝ => Real.pi-θ) (𝓝[<] Real.pi) (𝓝[>] (0:ℝ)) := by
    have hh := (show ContinuousWithinAt (fun θ : ℝ => Real.pi-θ) (Iio Real.pi) Real.pi from
      (continuous_const.sub continuous_id).continuousWithinAt).tendsto_nhdsWithin
      (show MapsTo (fun θ : ℝ => Real.pi-θ) (Iio Real.pi) (Ioi (0:ℝ)) by intro θ hθ; exact sub_pos.mpr (show θ < Real.pi from hθ))
    simpa using hh
  have hh := tendsto_neg_atBot_atTop.comp (angleGradient_zero_limit.comp ht)
  simpa only [Function.comp_def,angleGradient_pi_sub,neg_neg] using hh

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section

variable {I : Type*} [Fintype I]

def angleMove (x s t : ℝ) : ℝ := x+t*(s-x)

lemma angleMove_interior {x s t : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi)
    (hs : s ∈ Ioo (0:ℝ) Real.pi) (ht : t ∈ Ioo (0:ℝ) 1) :
    angleMove x s t ∈ Ioo (0:ℝ) Real.pi := by
  rcases hx with ⟨hx0,hxπ⟩
  rcases hs with ⟨hs0,hsπ⟩
  rcases ht with ⟨ht0,ht1⟩
  unfold angleMove
  have h0 := mul_nonneg (sub_nonneg.mpr ht1.le) hx0
  have h1 := mul_pos ht0 hs0
  have h2 := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hxπ)
  have h3 := mul_pos ht0 (sub_pos.mpr hsπ)
  constructor <;> nlinarith

lemma angleMove_hasDerivAt (x s t : ℝ) : HasDerivAt (angleMove x s) (s-x) t := by
  unfold angleMove
  simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const (s-x)).const_add x

def segmentGradient (x s : ℝ) (t : ℝ) := (s-x)*angleGradient (angleMove x s t)

lemma segmentGradient_boundary {x s : ℝ} (hs : s ∈ Ioo (0:ℝ) Real.pi)
    (hx : x=0 ∨ x=Real.pi) :
    Tendsto (segmentGradient x s) (𝓝[>] (0:ℝ)) atBot := by
  rcases hx with rfl | rfl
  · have ht : Tendsto (angleMove 0 s) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [angleMove] using (angleMove_hasDerivAt 0 s 0).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
        exact (angleMove_interior ⟨le_rfl,Real.pi_pos.le⟩ hs ht).1
    change Tendsto (fun t => (s-0)*angleGradient (angleMove 0 s t)) _ _
    simpa only [Function.comp_def] using
      (angleGradient_zero_limit.comp ht).const_mul_atBot (show 0 < s-0 by simpa using hs.1)
  · have ht : Tendsto (angleMove Real.pi s) (𝓝[>] (0:ℝ)) (𝓝[<] Real.pi) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [angleMove] using (angleMove_hasDerivAt Real.pi s 0).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
        exact (angleMove_interior ⟨Real.pi_pos.le,le_rfl⟩ hs ht).2
    exact (angleGradient_pi_limit.comp ht).const_mul_atTop_of_neg (sub_neg.mpr hs.2)

lemma segmentGradient_bounded_above {x s : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi)
    (hs : s ∈ Ioo (0:ℝ) Real.pi) :
    ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0:ℝ), segmentGradient x s t ≤ C := by
  by_cases hb : x=0 ∨ x=Real.pi
  · exact ⟨0,(segmentGradient_boundary hs hb).eventually (eventually_le_atBot 0)⟩
  · have hi : x ∈ Ioo (0:ℝ) Real.pi :=
      ⟨lt_of_le_of_ne hx.1 (fun h => hb (Or.inl h.symm)),
       lt_of_le_of_ne hx.2 (fun h => hb (Or.inr h))⟩
    have h : ContinuousAt (segmentGradient x s) 0 := by
      apply ContinuousAt.const_mul
      have hh : ContinuousAt angleGradient (angleMove x s 0) := by
        simpa only [angleMove,zero_mul,add_zero] using angleGradient_continuousAt hi
      exact hh.comp (angleMove_hasDerivAt x s 0).continuousAt
    refine ⟨segmentGradient x s 0+1,?_⟩
    exact (h.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (eventually_le_nhds (by linarith))

lemma sum_tendsto_atBot_of_one {F : I → ℝ → ℝ} {l : Filter ℝ} (j : I)
    (hj : Tendsto (F j) l atBot) (hB : ∀ i, ∃ C : ℝ, ∀ᶠ t in l, F i t ≤ C) :
    Tendsto (fun t => ∑ i, F i t) l atBot := by
  classical
  choose C hC using hB
  apply tendsto_atBot.mpr
  intro b
  have hc : ∀ᶠ t in l, ∀ i, F i t ≤ C i := Filter.eventually_all.mpr hC
  filter_upwards [hc,hj.eventually (eventually_le_atBot (b-∑ i ∈ Finset.univ.erase j,C i))] with t hCt hjt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hh := Finset.sum_le_sum (s:=Finset.univ.erase j) (fun i _ => hCt i)
  linarith

lemma entropy_segment_hasDerivAt (x s : I → ℝ) {t : ℝ}
    (hx : ∀ i, x i ∈ Icc (0:ℝ) Real.pi) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => ∑ i, angleEntropy (angleMove (x i) (s i) u))
      (∑ i, segmentGradient (x i) (s i) t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  unfold segmentGradient
  convert! (angleEntropy_hasDerivAt (angleMove_interior (hx i) (hs i) ht)).comp t
      (angleMove_hasDerivAt (x i) (s i) t) using 1
  ring

theorem entropy_boundary_descent (x s : I → ℝ)
    (hx : ∀ i, x i ∈ Icc (0:ℝ) Real.pi) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (hb : ∃ j, x j=0 ∨ x j=Real.pi) :
    ∃ t ∈ Ioo (0:ℝ) 1,
      (∑ i, angleEntropy (angleMove (x i) (s i) t)) < ∑ i, angleEntropy (x i) := by
  obtain ⟨j,hj⟩ := hb
  have hg : Tendsto (fun t => ∑ i, segmentGradient (x i) (s i) t) (𝓝[>] (0:ℝ)) atBot :=
    sum_tendsto_atBot_of_one j (segmentGradient_boundary (hs j) hj)
      (fun i => segmentGradient_bounded_above (hx i) (hs i))
  have hn := hg.eventually (eventually_lt_atBot (0:ℝ))
  obtain ⟨ε,hε,hne⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let e : ℝ := min (ε/2) (1/2)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have heε : e<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he1 : e<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hanti : StrictAntiOn (fun t => ∑ i, angleEntropy (angleMove (x i) (s i) t)) (Icc 0 e) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · apply Continuous.continuousOn
      apply continuous_finsetSum
      intro i _
      exact angleEntropy_continuous.comp (by unfold angleMove; fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans he1⟩
      rw [(entropy_segment_hasDerivAt x s hx hs ht1).deriv]
      apply hne
      exact ⟨by rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht.1]; exact ht.2.trans heε,ht.1⟩
  refine ⟨e,⟨he,he1⟩,?_⟩
  simpa [angleMove] using hanti (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,he.le⟩)
    (show e∈Icc 0 e from ⟨he.le,le_rfl⟩) he

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def angleSum (x : I → ℝ) : ℝ := ∑ i, angleEntropy (x i)

def angleFeasible (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ) : Set (I → ℝ) :=
  {x | (∀ i, x i ∈ Icc (0:ℝ) Real.pi) ∧ ∀ j, L j x=b j}

lemma angleSum_continuous : Continuous (angleSum (I:=I)) := by
  apply continuous_finsetSum
  intro i _
  exact angleEntropy_continuous.comp (continuous_apply i)

omit [Fintype I] [Fintype J] in
lemma angleFeasible_compact (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ) :
    IsCompact (angleFeasible L b) := by
  have hc : IsClosed {x : I → ℝ | ∀ j, L j x=b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_eq (L j).continuous continuous_const)
  have heq : angleFeasible L b = (Set.univ.pi (fun _ : I => Icc (0:ℝ) Real.pi)) ∩
      {x | ∀ j, L j x=b j} := by
    ext x
    simp only [angleFeasible,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_pi,Set.mem_univ,true_implies]
  rw [heq]
  exact (isCompact_univ_pi (fun _ : I => isCompact_Icc)).inter_right hc

omit [Fintype J] in
theorem exists_interior_angle_minimizer (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (s : I → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi) (hsL : ∀ j, L j s=b j) :
    ∃ x : I → ℝ, (∀ i, x i ∈ Ioo (0:ℝ) Real.pi) ∧ (∀ j, L j x=b j) ∧
      IsMinOn angleSum (angleFeasible L b) x := by
  have hsK : s ∈ angleFeasible L b := ⟨fun i => ⟨(hs i).1.le,(hs i).2.le⟩,hsL⟩
  obtain ⟨x,hxK,hmin⟩ := (angleFeasible_compact L b).exists_isMinOn ⟨s,hsK⟩ angleSum_continuous.continuousOn
  have hnob : ¬∃ i, x i=0 ∨ x i=Real.pi := by
    intro hb
    obtain ⟨t,ht,hdes⟩ := entropy_boundary_descent x s hxK.1 hs hb
    have hyK : (fun i => angleMove (x i) (s i) t) ∈ angleFeasible L b := by
      constructor
      · intro i
        exact ⟨(angleMove_interior (hxK.1 i) (hs i) ht).1.le,
          (angleMove_interior (hxK.1 i) (hs i) ht).2.le⟩
      · intro j
        change L j (x + t • (s-x))=b j
        rw [map_add,map_smul,map_sub,hxK.2 j,hsL j]
        simp
    exact (not_lt_of_ge (hmin hyK)) hdes
  refine ⟨x,fun i => ⟨?_,?_⟩,hxK.2,hmin⟩
  · exact lt_of_le_of_ne (hxK.1 i).1 (fun h => hnob ⟨i,Or.inl h.symm⟩)
  · exact lt_of_le_of_ne (hxK.1 i).2 (fun h => hnob ⟨i,Or.inr h⟩)

lemma angleSum_line_derivative (x v : I → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) Real.pi) :
    HasDerivAt (fun t : ℝ => angleSum (x+t • v)) (∑ i, angleGradient (x i)*v i) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hinner : HasDerivAt (fun t : ℝ => x i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)
  have ho : HasDerivAt angleEntropy (angleGradient (x i)) (x i+0*v i) := by
    simpa only [zero_mul,add_zero] using angleEntropy_hasDerivAt (hx i)
  have hd := ho.comp 0 hinner
  exact hd

omit [Fintype J] in
lemma angle_minimizer_stationary (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (x : I → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) Real.pi) (hxL : ∀ j, L j x=b j)
    (hmin : IsMinOn angleSum (angleFeasible L b) x)
    (v : I → ℝ) (hv : ∀ j, L j v=0) : ∑ i, angleGradient (x i)*v i=0 := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ∈ Ioo (0:ℝ) Real.pi := by
    apply Filter.eventually_all.mpr
    intro i
    have h : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
    have hh := h.tendsto.eventually (Ioo_mem_nhds (show 0<x i+0*v i by simpa using (hx i).1)
      (show x i+0*v i<Real.pi by simpa using (hx i).2))
    exact hh
  have hm : IsLocalMin (fun t : ℝ => angleSum (x+t • v)) 0 := by
    filter_upwards [he] with t ht
    simp only [zero_smul,add_zero]
    apply hmin
    constructor
    · intro i
      exact ⟨(ht i).1.le,(ht i).2.le⟩
    · intro j
      rw [map_add,map_smul,hxL j,hv j,smul_zero,add_zero]
  exact hm.hasDerivAt_eq_zero (angleSum_line_derivative x v hx)

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem exists_angle_multipliers [DecidableEq I] (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (s : I → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi) (hsL : ∀ j, L j s=b j) :
    ∃ (x : I → ℝ) (c : J → ℝ), (∀ i, x i ∈ Ioo (0:ℝ) Real.pi) ∧ (∀ j, L j x=b j) ∧
      ∀ i, angleGradient (x i) = ∑ j, c j * L j (Pi.single i 1) := by
  classical
  obtain ⟨x,hx,hxL,hmin⟩ := exists_interior_angle_minimizer L b s hs hsL
  let K : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, angleGradient (x i) • LinearMap.proj i
  have hK (v : I → ℝ) : K v=∑ i, angleGradient (x i)*v i := by
    simp only [K,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]
  have hker : (⨅ j, LinearMap.ker (L j).toLinearMap) ≤ LinearMap.ker K := by
    intro v hv
    change K v=0
    rw [hK]
    apply angle_minimizer_stationary L b x hx hxL hmin v
    intro j
    exact ((Submodule.mem_iInf _).mp hv j)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨x,c,hx,hxL,fun i => ?_⟩
  have he := LinearMap.congr_fun hc (Pi.single i (1:ℝ))
  rw [hK] at he
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_eq_mul,
    Pi.single_apply,mul_ite,Finset.sum_ite_irrel,Finset.mem_univ,ite_true,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq] using he.symm

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set

noncomputable section
variable {F V : Type*} [Fintype F] [Fintype V] [DecidableEq F] [DecidableEq V]

def faceCornerSum (f : F) : ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin 3, ContinuousLinearMap.proj (f,k)

def vertexCornerSum (vertex : F × Fin 3 → V) (v : V) : ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  ∑ i : F × Fin 3, if vertex i=v then ContinuousLinearMap.proj i else 0

def cornerConstraint (vertex : F × Fin 3 → V) :
    (F ⊕ V) → ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  Sum.elim faceCornerSum (vertexCornerSum vertex)

omit [Fintype V] [DecidableEq F] in
lemma vertexCornerSum_apply (vertex : F × Fin 3 → V) (v : V) (θ : F × Fin 3 → ℝ) :
    vertexCornerSum vertex v θ=∑ i : F × Fin 3, if vertex i=v then θ i else 0 := by
  unfold vertexCornerSum
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

omit [Fintype F] in
lemma faceCornerSum_single (f : F) (i : F × Fin 3) :
    faceCornerSum f (Pi.single i 1) = if f=i.1 then 1 else 0 := by
  classical
  rcases i with ⟨g,k⟩
  by_cases hfg : f=g
  · subst g
    simp [faceCornerSum,ContinuousLinearMap.proj_apply,
      Pi.single_apply,Prod.mk.injEq]
  · simp [faceCornerSum,ContinuousLinearMap.proj_apply,Prod.mk.injEq,hfg]

omit [Fintype V] in
lemma vertexCornerSum_single (vertex : F × Fin 3 → V) (v : V) (i : F × Fin 3) :
    vertexCornerSum vertex v (Pi.single i 1) = if vertex i=v then 1 else 0 := by
  classical
  simp only [vertexCornerSum,sum_apply]
  have he : ∀ j : F × Fin 3,
      (if vertex j=v then ContinuousLinearMap.proj j else (0 : ((F × Fin 3) → ℝ) →L[ℝ] ℝ)) (Pi.single i 1) =
      if j=i then (if vertex i=v then 1 else 0) else 0 := by
    intro j
    by_cases hji : j=i
    · subst j
      by_cases hv : vertex i=v <;> simp [hv]
    · by_cases hv : vertex j=v <;> simp [hv,hji]
  simp_rw [he]
  simp

lemma exp_angleGradient {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    Real.exp (angleGradient θ)=Real.tan (θ/2) := by
  have hh := half_trig_pos hθ
  rw [Real.tan_eq_sin_div_cos,angleGradient,← Real.log_div hh.1.ne' hh.2.ne']
  exact Real.exp_log (div_pos hh.1 hh.2)

theorem coherent_angles_give_radii (vertex : F × Fin 3 → V) (target : V → ℝ)
    (s : F × Fin 3 → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (hsface : ∀ f, ∑ k : Fin 3, s (f,k)=Real.pi)
    (hsvertex : ∀ v, (∑ i : F × Fin 3, if vertex i=v then s i else 0)=target v) :
    ∃ (θ : F × Fin 3 → ℝ) (r : V → ℝ) (q : F → ℝ),
      (∀ i, θ i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, θ (f,k)=Real.pi) ∧
      (∀ v, (∑ i : F × Fin 3, if vertex i=v then θ i else 0)=target v) ∧
      (∀ v, 0<r v) ∧ (∀ f, 0<q f) ∧
      ∀ i, Real.tan (θ i/2)=q i.1/r (vertex i) := by
  classical
  let L := cornerConstraint vertex
  let b : F ⊕ V → ℝ := Sum.elim (fun _ => Real.pi) target
  have hsL : ∀ j, L j s=b j := by
    intro j
    cases j with
    | inl f => simpa [L,b,cornerConstraint,faceCornerSum,sum_apply] using hsface f
    | inr v =>
      simpa only [L,b,cornerConstraint,Sum.elim_inr,vertexCornerSum_apply] using hsvertex v
  obtain ⟨θ,c,hθ,hθL,hgrad⟩ := exists_angle_multipliers L b s hs hsL
  refine ⟨θ,(fun v => Real.exp (-c (Sum.inr v))),(fun f => Real.exp (c (Sum.inl f))),
    hθ,?_,?_,fun _ => Real.exp_pos _,fun _ => Real.exp_pos _,?_⟩
  · intro f
    simpa [L,b,cornerConstraint,faceCornerSum,sum_apply] using hθL (Sum.inl f)
  · intro v
    simpa only [L,b,cornerConstraint,Sum.elim_inr,vertexCornerSum_apply] using hθL (Sum.inr v)
  · intro i
    have he : angleGradient (θ i)=c (Sum.inl i.1)+c (Sum.inr (vertex i)) := by
      rw [hgrad, Fintype.sum_sum_type]
      simp only [L,cornerConstraint,Sum.elim_inl,Sum.elim_inr,
        faceCornerSum_single,vertexCornerSum_single,mul_ite,mul_one,mul_zero]
      simp [eq_comm]
    rw [← exp_angleGradient (hθ i),he,← Real.exp_sub]
    congr 1
    ring

end
end CannonPackingGeometry

end
section
noncomputable section
namespace CannonPackingGeometry
open Finset Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

def neighborFaces (R : V → F → Prop) [DecidableRel R] (S : Finset V) : Finset F :=
  univ.filter (fun f => ∃ v∈S, R v f)

omit [DecidableEq F] in
theorem weighted_hall_equiv (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ)
    (hcut : ∀ S : Finset V, ∑ v∈S, d v ≤ ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ e : (Σ v, Fin (d v)) ≃ (Σ f, Fin (c f)), ∀ a, R a.1 (e a).1 := by
  classical
  let A := Σ v, Fin (d v)
  let B := Σ f, Fin (c f)
  have hh : ∀ S : Finset A,
      S.card ≤ (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)).card := by
    intro S
    let T : Finset V := S.image Sigma.fst
    have hS : S ⊆ T.sigma (fun v => (univ : Finset (Fin (d v)))) := by
      intro a ha
      exact mem_sigma.mpr ⟨mem_image.mpr ⟨a,ha,rfl⟩,mem_univ _⟩
    have hN : (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)) =
        (neighborFaces R T).sigma (fun f => (univ : Finset (Fin (c f)))) := by
      ext b
      constructor
      · intro hb
        obtain ⟨a,ha,hR⟩ := (mem_filter.mp hb).2
        apply Finset.mem_sigma.mpr
        exact ⟨mem_filter.mpr ⟨mem_univ _,a.1,mem_image.mpr ⟨a,ha,rfl⟩,hR⟩,
          mem_univ _⟩
      · intro hb
        have hb' := Finset.mem_sigma.mp hb
        obtain ⟨v,hv,hR⟩ := (mem_filter.mp hb'.1).2
        obtain ⟨a,ha,hav⟩ := mem_image.mp hv
        apply mem_filter.mpr
        exact ⟨mem_univ _,a,ha,hav.symm ▸ hR⟩
    calc
      S.card ≤ (T.sigma (fun v => (univ : Finset (Fin (d v))))).card := card_le_card hS
      _ = ∑ v∈T, d v := by simp [card_sigma]
      _ ≤ ∑ f∈neighborFaces R T, c f := hcut T
      _ = (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)).card := by rw [hN,card_sigma]; simp only [card_univ,Fintype.card_fin]
  obtain ⟨g,hg,hgR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (a : A) (b : B) => R a.1 b.1)).mp hh
  have hcard : Fintype.card A = Fintype.card B := by
    simpa [A,B,Fintype.card_sigma] using htotal
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hcard⟩),hgR⟩

theorem integer_transport (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ)
    (hcut : ∀ S : Finset V, ∑ v∈S, d v ≤ ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ w : V → F → ℕ,
      (∀ v, ∑ f, w v f = d v) ∧ (∀ f, ∑ v, w v f = c f) ∧
      ∀ v f, ¬R v f → w v f=0 := by
  classical
  obtain ⟨e,he⟩ := weighted_hall_equiv R d c hcut htotal
  let A := Σ v, Fin (d v)
  let B := Σ f, Fin (c f)
  let w : V → F → ℕ := fun v f =>
    ∑ a : A, if a.1=v ∧ (e a).1=f then 1 else 0
  refine ⟨w,?_,?_,?_⟩
  · intro v
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ a : A, ∑ f, if a.1=v ∧ (e a).1=f then 1 else 0) =
          ∑ a : A, if a.1=v then 1 else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases ha : a.1=v <;> simp [ha]
      _ = d v := by
        change (∑ a : (Σ v, Fin (d v)), if a.1=v then 1 else 0)=d v
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ x : V, if x=v then d x else 0 := by
            apply sum_congr rfl
            intro x _
            by_cases h : x=v <;> simp [h]
          _ = d v := by simp
  · intro f
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ a : A, ∑ v, if a.1=v ∧ (e a).1=f then 1 else 0) =
          ∑ a : A, if (e a).1=f then 1 else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases ha : (e a).1=f <;> simp [ha]
      _ = ∑ b : B, if b.1=f then 1 else 0 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = c f := by
        change (∑ b : (Σ f, Fin (c f)), if b.1=f then 1 else 0)=c f
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ x : F, if x=f then c x else 0 := by
            apply sum_congr rfl
            intro x _
            by_cases h : x=f <;> simp [h]
          _ = c f := by simp
  · intro v f hnot
    apply sum_eq_zero
    intro a _
    split_ifs with h
    · exact (hnot (h.1 ▸ h.2 ▸ he a)).elim
    · rfl

end CannonPackingGeometry

namespace CannonPackingGeometry
open Finset Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem positive_transport (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ) (hd : ∀ v, 0<d v) (hc : ∀ f, 0<c f)
    (hactive : ∀ f, ∃ v, R v f)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ →
      (∑ v∈S, d v) < ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ w : V → F → ℝ,
      (∀ v f, R v f → 0<w v f) ∧ (∀ v f, ¬R v f → w v f=0) ∧
      (∀ v, ∑ f, w v f = d v) ∧ (∀ f, ∑ v, w v f = c f) := by
  classical
  let dv : V → ℕ := fun v => ∑ f, if R v f then 1 else 0
  let df : F → ℕ := fun f => ∑ v, if R v f then 1 else 0
  let E : ℕ := ∑ v, dv v
  let Q : ℕ := E+1
  have hQ : 0<Q := Nat.succ_pos _
  have hE : ∑ f, df f=E := by dsimp [E,dv,df]; rw [sum_comm]
  have hdv (v : V) : dv v ≤ Q*d v := by
    have hh : dv v≤E := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    have hp : 1≤d v := hd v
    have hQE : E<Q := Nat.lt_succ_self _
    nlinarith
  have hdf (f : F) : df f ≤ Q*c f := by
    have hh : df f≤E := (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ f)).trans_eq hE
    have hp : 1≤c f := hc f
    have hQE : E<Q := Nat.lt_succ_self _
    nlinarith
  let D : V → ℕ := fun v => Q*d v-dv v
  let C : F → ℕ := fun f => Q*c f-df f
  have hD (S : Finset V) : (∑ v∈S,D v)+(∑ v∈S,dv v)=Q*(∑ v∈S,d v) := by
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel (hdv v))
  have hC (T : Finset F) : (∑ f∈T,C f)+(∑ f∈T,df f)=Q*(∑ f∈T,c f) := by
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun f _ => Nat.sub_add_cancel (hdf f))
  have hfull : ∑ v,D v=∑ f,C f := by
    have hv := hD univ
    have hf := hC univ
    rw [hE,←htotal] at hf
    change (∑ v,D v)+E=Q*(∑ v,d v) at hv
    omega
  have hrescut (S : Finset V) : ∑ v∈S,D v ≤ ∑ f∈neighborFaces R S,C f := by
    by_cases hs : S=∅
    · subst S
      simp
    by_cases ht : S=univ
    · subst S
      have hn : neighborFaces R univ=univ := by
        ext f
        simp only [neighborFaces,mem_filter,mem_univ,true_and]
        exact iff_true_intro (by obtain ⟨v,hv⟩ := hactive f; exact ⟨v,hv⟩)
      rw [hn]
      exact hfull.le
    have hgap := hcut S (nonempty_iff_ne_empty.mpr hs) ht
    have hmul := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt hgap)
    simp only [Nat.succ_eq_add_one,mul_add,mul_one] at hmul
    have hv := hD S
    have hf := hC (neighborFaces R S)
    have hde : ∑ f∈neighborFaces R S, df f ≤ E := by
      rw [←hE]
      exact sum_le_sum_of_subset (subset_univ _)
    have hQE : E<Q := Nat.lt_succ_self _
    rw [←hv,←hf] at hmul
    omega
  obtain ⟨w,hwv,hwf,hwzero⟩ := integer_transport R D C hrescut hfull
  let p : V → F → ℕ := fun v f => w v f + if R v f then 1 else 0
  have hpv (v : V) : ∑ f,p v f=Q*d v := by
    simp only [p,sum_add_distrib,hwv]
    exact Nat.sub_add_cancel (hdv v)
  have hpf (f : F) : ∑ v,p v f=Q*c f := by
    simp only [p,sum_add_distrib,hwf]
    exact Nat.sub_add_cancel (hdf f)
  have hpzero (v : V) (f : F) (h : ¬R v f) : p v f=0 := by simp [p,h,hwzero v f h]
  refine ⟨fun v f => (p v f : ℝ)/(Q:ℝ),?_,?_,?_,?_⟩
  · intro v f hR
    apply div_pos
    · exact_mod_cast (show 0<p v f by simp [p,hR])
    · exact_mod_cast hQ
  · intro v f hR
    change (p v f : ℝ)/(Q:ℝ)=0
    rw [hpzero v f hR]
    simp
  · intro v
    rw [←sum_div,←Nat.cast_sum,hpv,Nat.cast_mul]
    exact mul_div_cancel_left₀ (d v : ℝ) (by exact_mod_cast hQ.ne')
  · intro f
    rw [←sum_div,←Nat.cast_sum,hpf,Nat.cast_mul]
    exact mul_div_cancel_left₀ (c f : ℝ) (by exact_mod_cast hQ.ne')

end CannonPackingGeometry

end
end
end
end
end

end OAI
