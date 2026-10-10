import Mathlib
import OAI.Probability.SLELocalization.AngularClock
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Is Loewner Trace Using estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma visit_liveDistanceApproach (h : IsLoewnerTraceUsing driver γ g f)
    {z : ℂ} {v : ℝ} (hv : 0 < v) (hsmall : 2*v < z.im)
    (hvisit : ∃ T : ℝ, 0 ≤ T ∧ dist z (γ T) < v) :
    liveDistanceApproach γ z (3*v) := by
  obtain ⟨T,hT,hvisit⟩ := hvisit
  let TN : ℝ≥0 := ⟨T,hT⟩
  have hc : Continuous (fun t : ℝ≥0 => dist z (γ t)) :=
    continuous_const.dist (h.1.comp_continuous continuous_subtype_val (fun t => t.coe_nonneg))
  let A : Set ℝ≥0 := Icc 0 TN ∩ {t | dist z (γ t) ≤ 2*v}
  have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_le hc continuous_const)
  obtain ⟨s,hs,hmin⟩ := hA.exists_isLeast ⟨TN,⟨⟨zero_le,le_rfl⟩,by change dist z (γ T) ≤ 2*v; linarith⟩⟩
  have hsT : (s:ℝ) ≤ T := hs.1.2
  have hstrict (q : ℝ≥0) (hqs : q < s) : 2*v < dist z (γ q) := by
    by_contra hn
    exact (not_le_of_gt hqs) (hmin ⟨⟨zero_le,hqs.le.trans hs.1.2⟩,not_lt.1 hn⟩)
  have hinit : 2*v < dist z (γ 0) := by
    rw [h.2.1,dist_zero_right]
    exact hsmall.trans_le (Complex.im_le_norm z)
  have hdist : dist z (γ s) = 2*v := by
    apply le_antisymm hs.2
    by_contra hn
    have hl : dist z (γ s) < 2*v := not_le.1 hn
    have hcc : ContinuousOn (fun q : ℝ => dist z (γ q)) (Icc 0 (s:ℝ)) :=
      (continuous_const.dist continuous_id).comp_continuousOn (h.1.mono Icc_subset_Ici_self)
    obtain ⟨q,hq,he⟩ := intermediate_value_Icc' s.coe_nonneg hcc ⟨hl.le,hinit.le⟩
    have hqs : q < (s:ℝ) := lt_of_le_of_ne hq.2 (by intro heq; subst q; linarith)
    have hh := hstrict ⟨q,hq.1⟩ hqs
    change 2*v < dist z (γ q) at hh
    exact (not_lt_of_ge he.le) hh
  have hbefore (q : ℝ) (hq : q ∈ Icc 0 (s:ℝ)) : 2*v ≤ dist z (γ q) := by
    rcases lt_or_eq_of_le hq.2 with hh | hh
    · exact (hstrict ⟨q,hq.1⟩ hh).le
    · rw [hh,hdist]
  have hfree : ball z (2*v) ⊆ halfPlane \ localizationSegment γ 0 s := by
    intro w hw
    have hnorm : ‖w-z‖ < 2*v := by simpa only [mem_ball,dist_eq_norm] using hw
    constructor
    · have hh := Complex.abs_im_le_norm (w-z)
      have hn := neg_abs_le (w-z).im
      change 0 < w.im
      simp only [Complex.sub_im] at hh hn
      linarith
    · rintro ⟨q,hq,rfl⟩
      have hh := hbefore q hq
      have hh' := mem_ball.1 hw
      rw [dist_comm] at hh'
      linarith
  have hcl := h.future_tip_mem_closure s.coe_nonneg hsT
  have hb : γ T ∈ ball z (2*v) := by rw [mem_ball,dist_comm]; linarith
  obtain ⟨w,hwb,hwD⟩ := mem_closure_iff.1 hcl (ball z (2*v)) isOpen_ball hb
  have hcomp := (convex_ball z (2*v)).isPreconnected.subset_connectedComponentIn hwb hfree
  have hzball : z ∈ ball z (2*v) := mem_ball_self (by positivity)
  have hzlive : z ∈ localizationDomain γ s := by
    refine ⟨hfree hzball,?_⟩
    rw [← connectedComponentIn_eq (hcomp hzball)]
    exact hwD.2
  refine ⟨s,hzlive,?_⟩
  have hnot : γ s ∈ (localizationDomain γ s)ᶜ := by
    intro hh
    exact hh.1.2 ⟨s,⟨s.coe_nonneg,le_rfl⟩,rfl⟩
  have hh := infDist_le_dist_of_mem (x := z) hnot
  rw [hdist] at hh
  linarith

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SmallTarget

lemma sqrt_rpow {ε : ℝ} (hε : 0 ≤ ε) (β : ℝ) : (Real.sqrt ε)^β=ε^(β/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hε]
  congr 1
  ring

lemma interior_weight {p b ε : ℝ} {z : ℂ} (hp : 0 ≤ p) (hb : 0 ≤ b)
    (hε : 0 < ε) (hy : Real.sqrt ε ≤ z.im) :
    (2*z.im)^(-p)*(z.im/‖z‖)^b ≤ ε^(-(p/2)) := by
  have hyr : 0 < z.im := (Real.sqrt_pos.2 hε).trans_le hy
  have hn : 0 < ‖z‖ := hyr.trans_le (Complex.im_le_norm z)
  have hsin0 : 0 ≤ z.im/‖z‖ := div_nonneg hyr.le hn.le
  have hsin1 : z.im/‖z‖ ≤ 1 := (div_le_one hn).2 (Complex.im_le_norm z)
  have hsin := Real.rpow_le_one hsin0 hsin1 hb
  have hrad : (2*z.im)^(-p) ≤ (Real.sqrt ε)^(-p) :=
    Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hε) (by linarith) (neg_nonpos.mpr hp)
  calc
    _ ≤ (2*z.im)^(-p)*1 := mul_le_mul_of_nonneg_left hsin (Real.rpow_nonneg (by positivity) _)
    _ ≤ (Real.sqrt ε)^(-p) := by simpa using hrad
    _ = ε^(-(p/2)) := by rw [sqrt_rpow hε.le]; congr 1; ring

lemma interior_power_product {ε C p : ℝ} (hε : 0 < ε) :
    C*ε^(-(p/2))*(3*ε)^p = C*3^p*ε^(p/2) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) hε.le]
  calc
    _ = C*3^p*(ε^(-(p/2))*ε^p) := by ring
    _ = _ := by rw [← Real.rpow_add hε]; congr 2; ring

lemma radius_power {A ε β : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) :
    (A*Real.sqrt ε)^β=A^β*ε^(β/2) := by
  rw [Real.mul_rpow hA (Real.sqrt_nonneg _),sqrt_rpow hε]

theorem interior_trace_bound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (ε : ℝ) (_hε : 0 < ε) (_hy : Real.sqrt ε ≤ z.im)
      (_hsmall : 3*ε < c*z.im),
      P {sample | ∃ t : ℝ, 0 ≤ t ∧ dist z (γ sample t) < ε} ≤
        ENNReal.ofReal (C*ε^(codimension κ/2)) := by
  obtain ⟨C,c,hC,hc,hc1,hbound⟩ := euclideanApproachBound κ hκ
  have hp : 0 < codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have hb : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
  refine ⟨C*3^(codimension κ),c,mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),hc,hc1,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z ε hε hy hsmall
  have hz : z ∈ halfPlane := (Real.sqrt_pos.2 hε).trans_le hy
  have hsm : 2*ε < z.im := by
    have hh := mul_lt_mul_of_pos_right hc1 (show 0 < z.im from hz)
    linarith
  have hsub : {sample | ∃ t : ℝ, 0 ≤ t ∧ dist z (γ sample t) < ε} ≤ᵐ[P]
      {sample | liveDistanceApproach (γ sample) z (3*ε)} := by
    filter_upwards [hmaps] with sample hm hh
    exact hm.visit_liveDistanceApproach hε hsm hh
  refine (measure_mono_ae hsub).trans ((hbound P B hB γ g f hγ hmaps z hz (3*ε) (by positivity) hsmall).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hm := interior_weight hp.le hb.le hε hy
  have hpε : 0 ≤ (3*ε)^(codimension κ) := Real.rpow_nonneg (by positivity) _
  calc
    C*((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))*(3*ε)^(codimension κ) ≤
        C*ε^(-(codimension κ/2))*(3*ε)^(codimension κ) := by gcongr
    _ = C*3^(codimension κ)*ε^(codimension κ/2) := interior_power_product hε

end SLEExactGauge.SmallTarget

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.SmallTarget

lemma epsilon_le_sqrt {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : ε ≤ Real.sqrt ε := by
  have hs := Real.sq_sqrt hε
  have hp := Real.sqrt_nonneg ε
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1)]

lemma near_real_geometry {v : ℂ} {ε K : ℝ} (hv : 0 ≤ v.im) (hn : 1/2 ≤ ‖v‖)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (_hK : 0 ≤ K)
    (hy : v.im ≤ K*Real.sqrt ε) (hsmall : (K+1)*Real.sqrt ε < 1/4) :
    1/4 ≤ |v.re| ∧ ∀ w : ℂ, dist v w < ε → dist w (v.re:ℂ) < (K+1)*Real.sqrt ε := by
  have hs := Real.sqrt_nonneg ε
  have hy4 : v.im < 1/4 := by nlinarith
  have hab := Complex.norm_le_abs_re_add_abs_im v
  rw [abs_of_nonneg hv] at hab
  refine ⟨by linarith,?_⟩
  intro w hw
  have hvx : dist v (v.re:ℂ) ≤ v.im := by
    rw [dist_eq_norm]
    have hh := Complex.norm_le_abs_re_add_abs_im (v-(v.re:ℂ))
    simpa only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      sub_self,sub_zero,abs_zero,zero_add,abs_of_nonneg hv] using hh
  have he := epsilon_le_sqrt hε.le hε1
  calc
    dist w (v.re:ℂ) ≤ dist w v+dist v (v.re:ℂ) := dist_triangle _ _ _
    _ < ε+v.im := add_lt_add_of_lt_of_le (by simpa only [dist_comm] using hw) hvx
    _ ≤ (K+1)*Real.sqrt ε := by nlinarith

lemma cutoff_sqrt_small {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hsmall : ε < 1/(16*A^2)) : A*Real.sqrt ε < 1/4 := by
  have hh := (lt_div_iff₀ (show 0 < 16*A^2 by positivity)).mp hsmall
  have hs := Real.sq_sqrt hε.le
  have hp : 0 ≤ A*Real.sqrt ε := by positivity
  nlinarith [sq_nonneg (A*Real.sqrt ε-1/4)]

end SLEExactGauge.SmallTarget

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open SmallTarget BoundaryGreen

theorem uniform_small_target (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (v : ℂ), 0 ≤ v.im → 1/2 ≤ ‖v‖ → ‖v‖ ≤ 2 →
        ∀ ε : ℝ, 0 < ε → ε < 1/16 →
        P {sample | ∃ t : ℝ, 0 ≤ t ∧ dist v (γ sample t) < ε} ≤
          ENNReal.ofReal (C*ε^c) := by
  let β := (8/κ-1)/2
  let a := 1+κ/8
  obtain ⟨hβ,ha,ha2,hba⟩ := exponent_choice hκ.1 hκ.2
  change 0 < β at hβ
  change 0 < a at ha
  change a < 2 at ha2
  change κ*(β+1) < 4+2*a at hba
  let δ := (2-a)/8
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhalf : δ ≤ 1/2 := by dsimp [δ]; linarith
  have haδ : a ≤ 2-4*δ := by dsimp [δ]; linarith
  obtain ⟨Ci,e,hi,he,he1,hinter⟩ := interior_trace_bound κ hκ
  let K := max 1 (3/e)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKe : 3/e ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  let A := K+1
  have hA : 0 < A := by dsimp [A]; positivity
  let ρ := 1/(16*A^2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let c := min (β/2) (codimension κ/2)
  have hp : 0 < codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have hc : 0 < c := lt_min (half_pos hβ) (half_pos hp)
  let Cb := (16/δ)^β*A^β
  have hCb : 0 < Cb := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hA _)
  let C := Cb+Ci+ρ^(-c)
  have hR : 0 < ρ^(-c) := Real.rpow_pos_of_pos hρ _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbC : Cb ≤ C := by dsimp only [C]; linarith
  have hiC : Ci ≤ C := by dsimp only [C]; linarith
  have hrC : ρ^(-c) ≤ C := by dsimp only [C]; linarith
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps v hv hn hlo ε hε hε16
  have hε1 : ε ≤ 1 := by linarith
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have heps := epsilon_le_sqrt hε.le hε1
  by_cases hsmall : ε < ρ
  · by_cases hnear : v.im ≤ K*Real.sqrt ε
    · have hgeom := near_real_geometry hv hn hε hε1 hK.le hnear (cutoff_sqrt_small hA hε hsmall)
      have hsub : {sample | ∃ t : ℝ, 0 ≤ t ∧ dist v (γ sample t) < ε} ⊆
          {sample | ∃ t : ℝ, 0 ≤ t ∧ dist (γ sample t) (v.re:ℂ) < A*Real.sqrt ε} := by
        rintro sample ⟨t,ht,hclose⟩
        exact ⟨t,ht,hgeom.2 _ hclose⟩
      have hh := annulus_real_bound hB κ β a δ hκ.1.le hβ ha.le hba.le hδ hδhalf haδ
        γ g f hmaps hgeom.1 (mul_pos hA hs)
      refine (measure_mono hsub).trans (hh.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [radius_power hA.le hε.le]
      have hepow : ε^(β/2) ≤ ε^c := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
      calc
        (16/δ)^β*(A^β*ε^(β/2)) = Cb*ε^(β/2) := by dsimp only [Cb]; ring
        _ ≤ Cb*ε^c := mul_le_mul_of_nonneg_left hepow hCb.le
        _ ≤ C*ε^c := mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hε.le _)
    · have hy : Real.sqrt ε ≤ v.im := by
        have hh := mul_le_mul_of_nonneg_right hK1 hs.le
        linarith [not_le.mp hnear]
      have hm : 3*ε < e*v.im := by
        have hh := (div_le_iff₀ he).mp hKe
        have hm := mul_le_mul_of_nonneg_right hh hs.le
        have hlt := mul_lt_mul_of_pos_left (not_le.mp hnear) he
        nlinarith
      refine (hinter P B hB γ g f hγ hmaps v ε hε hy hm).trans (ENNReal.ofReal_le_ofReal ?_)
      have hepow : ε^(codimension κ/2) ≤ ε^c := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
      exact (mul_le_mul_of_nonneg_left hepow hi.le).trans
        (mul_le_mul_of_nonneg_right hiC (Real.rpow_nonneg hε.le _))
  · have hrε := Real.rpow_le_rpow hρ.le (not_lt.1 hsmall) hc.le
    have hprod : ρ^(-c)*ρ^c = 1 := by
      rw [Real.rpow_neg hρ.le,inv_mul_cancel₀ (Real.rpow_pos_of_pos hρ _).ne']
    have h1 : 1 ≤ C*ε^c := by
      calc
        1 = ρ^(-c)*ρ^c := hprod.symm
        _ ≤ ρ^(-c)*ε^c := mul_le_mul_of_nonneg_left hrε hR.le
        _ ≤ C*ε^c := mul_le_mul_of_nonneg_right hrC (Real.rpow_nonneg hε.le _)
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SmallTarget

lemma scaled_near_real_geometry {v : ℂ} {R ε K : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v.im) (hn : R/2 ≤ ‖v‖) (hε : 0 < ε) (hε1 : ε ≤ 1) (_hK : 0 ≤ K)
    (hy : v.im ≤ R*(K*Real.sqrt ε)) (hsmall : (K+1)*Real.sqrt ε < 1/4) :
    R/4 ≤ |v.re| ∧ ∀ w : ℂ, dist v w < R*ε →
      dist w (v.re:ℂ) < R*((K+1)*Real.sqrt ε) := by
  have hs := Real.sqrt_nonneg ε
  have hmul := mul_lt_mul_of_pos_left hsmall hR
  have hy4 : v.im < R/4 := by nlinarith [mul_nonneg hR.le hs]
  have hab := Complex.norm_le_abs_re_add_abs_im v
  rw [abs_of_nonneg hv] at hab
  refine ⟨by linarith,?_⟩
  intro w hw
  have hvx : dist v (v.re:ℂ) ≤ v.im := by
    rw [dist_eq_norm]
    have hh := Complex.norm_le_abs_re_add_abs_im (v-(v.re:ℂ))
    simpa only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      sub_self,sub_zero,abs_zero,zero_add,abs_of_nonneg hv] using hh
  have he := mul_le_mul_of_nonneg_left (epsilon_le_sqrt hε.le hε1) hR.le
  calc
    dist w (v.re:ℂ) ≤ dist w v+dist v (v.re:ℂ) := dist_triangle _ _ _
    _ < R*ε+v.im := add_lt_add_of_lt_of_le (by simpa only [dist_comm] using hw) hvx
    _ ≤ R*((K+1)*Real.sqrt ε) := by nlinarith

lemma scaled_interior_power {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    (R*Real.sqrt ε)^(-p)*(3*(R*ε))^p = 3^p*ε^(p/2) := by
  rw [Real.mul_rpow hR.le (Real.sqrt_nonneg _),sqrt_rpow hε.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤3) (mul_nonneg hR.le hε.le),Real.mul_rpow hR.le hε.le]
  calc
    _ = 3^p*(R^(-p)*R^p)*(ε^(-p/2)*ε^p) := by ring
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hε,neg_add_cancel,Real.rpow_zero,mul_one,show -p/2+p=p/2 by ring]

 theorem interior_trace_scaled_bound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (R ε : ℝ) (_hR : 0 < R) (_hε : 0 < ε) (_hy : R*Real.sqrt ε ≤ z.im)
      (_hsmall : 3*(R*ε) < c*z.im),
      P {sample | ∃ t : ℝ, 0 ≤ t ∧ dist z (γ sample t) < R*ε} ≤
        ENNReal.ofReal (C*ε^(codimension κ/2)) := by
  obtain ⟨C,c,hC,hc,hc1,hbound⟩ := euclideanApproachBound κ hκ
  have hp : 0 < codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have hb : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
  refine ⟨C*3^(codimension κ),c,mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),hc,hc1,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z R ε hR hε hy hsmall
  have hs := Real.sqrt_pos.2 hε
  have hz : z ∈ halfPlane := (mul_pos hR hs).trans_le hy
  have hzim : 0 < z.im := hz
  have hsm : 2*(R*ε) < z.im := by
    have hh := mul_lt_mul_of_pos_right hc1 (show 0 < z.im from hz)
    linarith [mul_pos hR hε]
  have hsub : {sample | ∃ t : ℝ, 0 ≤ t ∧ dist z (γ sample t) < R*ε} ≤ᵐ[P]
      {sample | liveDistanceApproach (γ sample) z (3*(R*ε))} := by
    filter_upwards [hmaps] with sample hm hh
    exact hm.visit_liveDistanceApproach (mul_pos hR hε) hsm hh
  refine (measure_mono_ae hsub).trans ((hbound P B hB γ g f hγ hmaps z hz _ (by positivity) hsmall).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hn : 0 < ‖z‖ := hz.trans_le (Complex.im_le_norm z)
  have hsin := Real.rpow_le_one (div_nonneg hz.le hn.le)
    ((div_le_one hn).2 (Complex.im_le_norm z)) hb.le
  have hrad : (2*z.im)^(-codimension κ) ≤ (R*Real.sqrt ε)^(-codimension κ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hR hs) (by linarith [hzim]) (by linarith)
  calc
    _ ≤ C*((2*z.im)^(-codimension κ)*1)*(3*(R*ε))^(codimension κ)  := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsin (Real.rpow_nonneg (by positivity) _)) hC.le)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ C*((R*Real.sqrt ε)^(-codimension κ))*(3*(R*ε))^(codimension κ) := by
      simp only [mul_one]; gcongr
    _ = C*3^(codimension κ)*ε^(codimension κ/2) := by
      rw [mul_assoc,scaled_interior_power hR hε]; ring

end SLEExactGauge.SmallTarget

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open SmallTarget BoundaryGreen

lemma scaled_annulus_real_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a δ : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 < β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {x R d : ℝ} (hR : 0 < R) (hx : R/4 ≤ |x|) (hd : 0 < d) :
    P {ω | ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < R*d} ≤ ENNReal.ofReal ((16/δ)^β*d^β) := by
  have hxp : 0 < |x| := (by positivity : 0 < R/4).trans_le hx
  refine (real_bound hB κ β a δ hκ hβ ha hba hδ hδhalf haδ γ g f hmaps hxp (mul_pos hR hd)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hr : 4*(R*d)/(δ*|x|) ≤ (16/δ)*d := by
    rw [div_le_iff₀ (mul_pos hδ hxp)]
    have hh := mul_le_mul_of_nonneg_left hx (show 0 ≤ 16*d by positivity)
    field_simp
    nlinarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 4*(R*d)/(δ*|x|)) hr hβ.le
  rwa [Real.mul_rpow (by positivity : 0 ≤ 16/δ) hd.le] at hh

theorem uniform_small_target_scaled (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (v : ℂ) (R : ℝ), 0 < R → 0 ≤ v.im → R/2 ≤ ‖v‖ →
        ∀ ε : ℝ, 0 < ε → ε < 1/16 →
        P {sample | ∃ t : ℝ, 0 ≤ t ∧ dist v (γ sample t) < R*ε} ≤
          ENNReal.ofReal (C*ε^c) := by
  let β := (8/κ-1)/2
  let a := 1+κ/8
  obtain ⟨hβ,ha,ha2,hba⟩ := exponent_choice hκ.1 hκ.2
  change 0 < β at hβ
  change 0 < a at ha
  change a < 2 at ha2
  change κ*(β+1) < 4+2*a at hba
  let δ := (2-a)/8
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhalf : δ ≤ 1/2 := by dsimp [δ]; linarith
  have haδ : a ≤ 2-4*δ := by dsimp [δ]; linarith
  obtain ⟨Ci,e,hi,he,he1,hinter⟩ := interior_trace_scaled_bound κ hκ
  let K := max 1 (3/e)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKe : 3/e ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  let A := K+1
  have hA : 0 < A := by dsimp [A]; positivity
  let ρ := 1/(16*A^2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let c := min (β/2) (codimension κ/2)
  have hp : 0 < codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have hc : 0 < c := lt_min (half_pos hβ) (half_pos hp)
  let Cb := (16/δ)^β*A^β
  have hCb : 0 < Cb := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hA _)
  let C := Cb+Ci+ρ^(-c)
  have hρpow : 0 < ρ^(-c) := Real.rpow_pos_of_pos hρ _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbC : Cb ≤ C := by dsimp only [C]; linarith
  have hiC : Ci ≤ C := by dsimp only [C]; linarith
  have hrC : ρ^(-c) ≤ C := by dsimp only [C]; linarith
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps v R hR hv hn ε hε hε16
  have hε1 : ε ≤ 1 := by linarith
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have heps := epsilon_le_sqrt hε.le hε1
  by_cases hsmall : ε < ρ
  · by_cases hnear : v.im ≤ R*(K*Real.sqrt ε)
    · have hgeom := scaled_near_real_geometry hR hv hn hε hε1 hK.le hnear (cutoff_sqrt_small hA hε hsmall)
      have hsub : {sample | ∃ t : ℝ, 0 ≤ t ∧ dist v (γ sample t) < R*ε} ⊆
          {sample | ∃ t : ℝ, 0 ≤ t ∧ dist (γ sample t) (v.re:ℂ) < R*(A*Real.sqrt ε)} := by
        rintro sample ⟨t,ht,hclose⟩
        exact ⟨t,ht,hgeom.2 _ hclose⟩
      have hh := scaled_annulus_real_bound hB κ β a δ hκ.1.le hβ ha.le hba.le hδ hδhalf haδ
        γ g f hmaps hR hgeom.1 (mul_pos hA hs)
      refine (measure_mono hsub).trans (hh.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [radius_power hA.le hε.le]
      have hepow : ε^(β/2) ≤ ε^c := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
      calc
        (16/δ)^β*(A^β*ε^(β/2)) = Cb*ε^(β/2) := by dsimp only [Cb]; ring
        _ ≤ Cb*ε^c := mul_le_mul_of_nonneg_left hepow hCb.le
        _ ≤ C*ε^c := mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hε.le _)
    · have hy : R*Real.sqrt ε ≤ v.im := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hK1 hs.le) hR.le
        nlinarith [not_le.mp hnear]
      have hm : 3*(R*ε) < e*v.im := by
        have hh := (div_le_iff₀ he).mp hKe
        calc
          3*(R*ε) ≤ 3*(R*Real.sqrt ε) := by gcongr
          _ ≤ e*(R*(K*Real.sqrt ε)) := by
            have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg hR.le hs.le)
            nlinarith
          _ < e*v.im := mul_lt_mul_of_pos_left (not_le.mp hnear) he
      refine (hinter P B hB γ g f hγ hmaps v R ε hR hε hy hm).trans (ENNReal.ofReal_le_ofReal ?_)
      have hepow : ε^(codimension κ/2) ≤ ε^c := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
      exact (mul_le_mul_of_nonneg_left hepow hi.le).trans
        (mul_le_mul_of_nonneg_right hiC (Real.rpow_nonneg hε.le _))
  · have hrε := Real.rpow_le_rpow hρ.le (not_lt.1 hsmall) hc.le
    have hprod : ρ^(-c)*ρ^c = 1 := by
      rw [Real.rpow_neg hρ.le,inv_mul_cancel₀ (Real.rpow_pos_of_pos hρ _).ne']
    have h1 : 1 ≤ C*ε^c := by
      calc
        1 = ρ^(-c)*ρ^c := hprod.symm
        _ ≤ ρ^(-c)*ε^c := mul_le_mul_of_nonneg_left hrε hρpow.le
        _ ≤ C*ε^c := mul_le_mul_of_nonneg_right hrC (Real.rpow_nonneg hε.le _)
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def logTrace {Ω : Type*} (γ : Ω → ℝ → ℂ) (ω : Ω) : Set (ℝ × ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ γ ω t = Complex.exp ((x.1:ℂ)+(x.2:ℂ)*Complex.I)}

lemma dyadic_radius_power (K c : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (K/(2:ℝ)^n)^c = K^c*((1/2:ℝ)^c)^n := by
  rw [div_eq_mul_inv,Real.mul_rpow hK (by positivity),← inv_pow,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  simp only [one_div]

theorem logTrace_dyadic_hitting (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C₀ ρ : ℝ, 0 < C₀ ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (j : ℝ) (n : ℕ) (i : DIndex n),
          P {ω | ∃ x ∈ logTrace γ ω, x ∈ (dyadicRect (unitSlab j) n i).closed} ≤
            ENNReal.ofReal (C₀*ρ^n) := by
  obtain ⟨C,c,hC,hc,hsmall⟩ := uniform_small_target_scaled κ hκ
  let K := expCellScale
  let ρ := (1/2:ℝ)^c
  let C₀ := (C+16^c)*K^c
  have hK : 0 < K := expCellScale_pos
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hc
  have h16 : 0 < (16:ℝ)^c := Real.rpow_pos_of_pos (by norm_num) _
  have hC₀ : 0 < C₀ := mul_pos (add_pos hC h16) (Real.rpow_pos_of_pos hK _)
  refine ⟨C₀,ρ,hC₀,hρ,hρ1,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps j n i
  let ε := K/(2:ℝ)^n
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : ε^c = K^c*ρ^n := dyadic_radius_power K c hK.le n
  by_cases hεsmall : ε < 1/16
  · let Q := dyadicRect (unitSlab j) n i
    let v := Complex.exp ((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)
    have hg := dyadicCell_exp_geometry j n i hεsmall
    have hb := hsmall P B hB γ g f hγ hmaps v (Real.exp j) (Real.exp_pos _) hg.1 hg.2.1 ε hε hεsmall
    have hs : {ω | ∃ x ∈ logTrace γ ω, x ∈ Q.closed} ⊆
        {ω | ∃ t : ℝ, 0 ≤ t ∧ dist v (γ ω t) < Real.exp j*ε} := by
      rintro ω ⟨x,⟨t,ht,he⟩,hx⟩
      refine ⟨t,ht,?_⟩
      rw [he]
      exact hg.2.2 x hx
    refine (measure_mono hs).trans (hb.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [heq]
    change C*(K^c*ρ^n) ≤ ((C+16^c)*K^c)*ρ^n
    nlinarith [mul_nonneg h16.le (mul_nonneg (Real.rpow_nonneg hK.le c) (pow_nonneg hρ.le n))]
  · have hbase : 1 ≤ 16*ε := by linarith [not_lt.mp hεsmall]
    have hp := Real.one_le_rpow hbase hc.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤16) hε.le,heq] at hp
    have h1 : 1 ≤ C₀*ρ^n := hp.trans (by
      change 16^c*(K^c*ρ^n) ≤ ((C+16^c)*K^c)*ρ^n
      nlinarith [mul_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hK.le c) (pow_nonneg hρ.le n))])
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
namespace DRect

instance (Q : DRect) : IsFiniteMeasure Q.measure := by unfold measure; infer_instance

lemma measure_subset {Q R : DRect} (ha : Q.a ≤ R.a) (hb : R.b ≤ Q.b)
    (hc : Q.c ≤ R.c) (hd : R.d ≤ Q.d) : R.measure ≤ Q.measure :=
  Measure.prod_mono (Measure.restrict_mono_set _ (fun _x hx => ⟨ha.trans_lt hx.1,hx.2.trans hb⟩))
    (Measure.restrict_mono_set _ (fun _y hy => ⟨hc.trans_lt hy.1,hy.2.trans hd⟩))

lemma child_measure_le (Q : DRect) (s : Bool × Bool) : (Q.child s).measure ≤ Q.measure := by
  obtain ⟨ha,hb,hc,hd⟩ := Q.child_bounds s
  exact measure_subset ha hb hc hd

lemma measure_interval_split {l r : ℝ} (h : l < r) :
    volume.restrict (Ioc l r) = volume.restrict (Ioc l ((l+r)/2))+
      volume.restrict (Ioc ((l+r)/2) r) := by
  rw [← Ioc_union_Ioc_eq_Ioc (show l ≤ (l+r)/2 by linarith) (show (l+r)/2 ≤ r by linarith)]
  apply Measure.restrict_union _ measurableSet_Ioc
  exact disjoint_left.2 (fun x hx hy => (not_lt_of_ge hx.2) hy.1)

lemma measure_child_sum (Q : DRect) : Q.measure = ∑ s : Bool × Bool, (Q.child s).measure := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,measure,child,halfLo,halfHi,↓reduceIte]
  rw [measure_interval_split Q.hab,measure_interval_split Q.hcd,Measure.add_prod,
    Measure.prod_add,Measure.prod_add]
  ac_rfl

end DRect

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma dyadicRect_measure_le (Q : DRect) (n : ℕ) (i : DIndex n) :
    (dyadicRect Q n i).measure ≤ Q.measure := by
  obtain ⟨ha,hb,hc,hd⟩ := dyadicRect_bounds Q n i
  exact DRect.measure_subset ha hb hc hd

lemma dyadic_measure_sum (Q : DRect) (n : ℕ) :
    Q.measure = ∑ i : DIndex n, (dyadicRect Q n i).measure := by
  induction n with
  | zero =>
    let : Unique (DIndex 0) := inferInstanceAs (Unique Unit)
    rw [Fintype.sum_unique]
    rfl
  | succ n ih =>
    change Q.measure = ∑ i : DIndex n × (Bool × Bool), ((dyadicRect Q n i.1).child i.2).measure
    rw [Fintype.sum_prod_type]
    simp_rw [← DRect.measure_child_sum]
    exact ih

lemma dyadic_integral_sum (Q : DRect) {g : ℝ × ℝ → ℝ} (hg : Integrable g Q.measure) (n : ℕ) :
    ∑ i : DIndex n, (∫ p, g p ∂(dyadicRect Q n i).measure) = ∫ p, g p ∂Q.measure := by
  conv_rhs => rw [dyadic_measure_sum Q n]
  symm
  exact integral_finsetSum_measure (fun i hi => hg.mono_measure (dyadicRect_measure_le Q n i))

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def jumpSize (H : ℝ) (j : ℕ) : ℝ := H/(8*((j:ℝ)+1)*((j:ℝ)+2))

lemma jumpSize_pos {H : ℝ} (hH : 0 < H) (j : ℕ) : 0 < jumpSize H j := by
  unfold jumpSize
  positivity

lemma jumpSize_telescope (H : ℝ) (j : ℕ) :
    H/8*(1-1/((j:ℝ)+1)) + jumpSize H j = H/8*(1-1/((j:ℝ)+2)) := by
  unfold jumpSize
  have h1 : (j:ℝ)+1 ≠ 0 := by positivity
  have h2 : (j:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

lemma exists_large_increment {H : ℝ} (hH : 0 < H) {v : ℕ → ℝ}
    (hstart : v 0 ≤ 3*H/4) (hlim : Tendsto v atTop (𝓝 H)) :
    ∃ j : ℕ, jumpSize H j < |v (j+1)-v j| := by
  by_contra hn
  push Not at hn
  have hb (n : ℕ) : v n ≤ v 0 + H/8*(1-1/((n:ℝ)+1)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := le_trans (le_abs_self (v (n+1)-v n)) (hn n)
      have hh := jumpSize_telescope H n
      have hc : ((n+1:ℕ):ℝ)+1 = (n:ℝ)+2 := by norm_num; ring
      rw [hc]
      linarith
  have hb' (n : ℕ) : v n ≤ 7*H/8 := by
    have hinv : 0 ≤ 1/((n:ℝ)+1) := by positivity
    have hp : 0 ≤ H/8 := by positivity
    have hm := mul_nonneg hp hinv
    linarith [hb n]
  have hh := le_of_tendsto hlim (Filter.Eventually.of_forall hb')
  linarith

lemma geometric_moment_summable {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => (((j:ℝ)+1)*((j:ℝ)+2))^2*q^j) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq] using hq1
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hn
  have h4 := summable_pow_mul_geometric_of_norm_lt_one 4 hn
  have hh := (((h4.add (h3.mul_left 6)).add (h2.mul_left 13)).add
    (h1.mul_left 12)).add (h0.mul_left 4)
  apply hh.congr
  intro j
  ring

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
section Tree
variable {X : Type} {I : ℕ → Type} [finiteIndex : ∀ n, Fintype (I n)]
  (parent : ∀ n, I (n+1) → I n) (branch : X → ∀ n, I n)
  (means energy : ∀ n, I n → ℝ) (value : X → ℝ)

omit finiteIndex in
lemma branch_bad_parent [∀ level, Fintype (I level)] {H D : ℝ} (hH : 0 < H) (N : ℕ)
    (hbranch : ∀ x n, parent n (branch x (n+1)) = branch x n)
    (hroot : ∀ i, means N i ≤ 3*H/4)
    (hstep : ∀ n i, |means (n+1) i - means n (parent n i)|^2 ≤ D*energy n (parent n i))
    (hlim : ∀ x, Tendsto (fun n => means n (branch x n)) atTop (𝓝 (value x)))
    {x : X} (hx : value x = H) :
    ∃ j : ℕ, (jumpSize H j)^2 < D*energy (N+j) (branch x (N+j)) := by
  have hl : Tendsto (fun n => means (N+n) (branch x (N+n))) atTop (𝓝 H) := by
    have ht : Tendsto (fun n : ℕ => N+n) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
    simpa only [Function.comp_def,hx] using (hlim x).comp ht
  obtain ⟨j,hj⟩ := exists_large_increment hH (by simpa using hroot (branch x N)) hl
  refine ⟨j,?_⟩
  have hs := hstep (N+j) (branch x ((N+j)+1))
  rw [hbranch] at hs
  have hj' : jumpSize H j < |means ((N+j)+1) (branch x ((N+j)+1)) - means (N+j) (branch x (N+j))| := by
    have he : N+(j+1) = (N+j)+1 := (Nat.add_assoc N j 1).symm
    rw [he] at hj
    exact hj
  exact ((sq_lt_sq₀ (jumpSize_pos hH j).le (abs_nonneg _)).2 hj').trans_le hs

end Tree

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma jump_energy_scale {H : ℝ} (hH : H ≠ 0) (D E C q : ℝ) (N j : ℕ) :
    D*E/(jumpSize H j)^2*(C*q^(N+j)) =
      (64*D*C*E/H^2*q^N)*((((j:ℝ)+1)*((j:ℝ)+2))^2*q^j) := by
  unfold jumpSize
  rw [pow_add]
  field_simp
  ring

theorem dyadic_energy_hitting
    {X : Type} {I : ℕ → Type} [∀ n, Fintype (I n)]
    (parent : ∀ n, I (n+1) → I n) (branch : X → ∀ n, I n)
    (means energy : ∀ n, I n → ℝ) (value : X → ℝ)
    {H D E C₀ q : ℝ} (hH : 0 < H) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hC : 0 ≤ C₀) (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (hbranch : ∀ x n, parent n (branch x (n+1)) = branch x n)
    (hroot : ∀ i, means N i ≤ 3*H/4)
    (hstep : ∀ n i, |means (n+1) i - means n (parent n i)|^2 ≤ D*energy n (parent n i))
    (hlim : ∀ x, Tendsto (fun n => means n (branch x n)) atTop (𝓝 (value x)))
    (hnon : ∀ n i, 0 ≤ energy n i) (hsum : ∀ n, ∑ i, energy n i ≤ E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Ξ : Ω → Set X)
    (hhit : ∀ n i, P {ω | ∃ x ∈ Ξ ω, branch x n = i} ≤ ENNReal.ofReal (C₀*q^n)) :
    P {ω | ∃ x ∈ Ξ ω, value x = H} ≤
      ENNReal.ofReal ((64*D*C₀*E/H^2*q^N)*
        ∑' j : ℕ, (((j:ℝ)+1)*((j:ℝ)+2))^2*q^j) := by
  classical
  let event (j : ℕ) (i : I (N+j)) : Set Ω :=
    {ω | (jumpSize H j)^2 < D*energy (N+j) i ∧ ∃ x ∈ Ξ ω, branch x (N+j) = i}
  have hcover : {ω | ∃ x ∈ Ξ ω, value x = H} ⊆ ⋃ j : ℕ, ⋃ i : I (N+j), event j i := by
    rintro ω ⟨x,hx,hv⟩
    obtain ⟨j,hj⟩ := branch_bad_parent parent branch means energy value hH N hbranch hroot hstep hlim hv
    exact mem_iUnion.2 ⟨j,mem_iUnion.2 ⟨branch x (N+j),hj,x,hx,rfl⟩⟩
  have hb (j : ℕ) (i : I (N+j)) :
      P (event j i) ≤ ENNReal.ofReal (D*energy (N+j) i/(jumpSize H j)^2*(C₀*q^(N+j))) := by
    by_cases hh : (jumpSize H j)^2 < D*energy (N+j) i
    · have hs : event j i ⊆ {ω | ∃ x ∈ Ξ ω, branch x (N+j) = i} := fun _ h => h.2
      refine (measure_mono hs).trans ((hhit _ _).trans (ENNReal.ofReal_le_ofReal ?_))
      have hratio : 1 ≤ D*energy (N+j) i/(jumpSize H j)^2 :=
        (le_div_iff₀ (sq_pos_of_pos (jumpSize_pos hH j))).2 (by simpa using hh.le)
      exact le_mul_of_one_le_left (mul_nonneg hC (pow_nonneg hq _)) hratio
    · have he : event j i = ∅ := by ext ω; simp [event,hh]
      rw [he,measure_empty]
      exact bot_le
  have hlevel (j : ℕ) : P (⋃ i : I (N+j), event j i) ≤
      ENNReal.ofReal (D*E/(jumpSize H j)^2*(C₀*q^(N+j))) := by
    calc
      _ ≤ ∑ i : I (N+j), P (event j i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ i : I (N+j), ENNReal.ofReal (D*energy (N+j) i/(jumpSize H j)^2*(C₀*q^(N+j))) :=
        Finset.sum_le_sum (fun i _ => hb j i)
      _ = ENNReal.ofReal (∑ i : I (N+j), D*energy (N+j) i/(jumpSize H j)^2*(C₀*q^(N+j))) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i hi
        exact mul_nonneg (div_nonneg (mul_nonneg hD (hnon _ _)) (sq_nonneg _))
          (mul_nonneg hC (pow_nonneg hq _))
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        simp only [← Finset.sum_mul,← Finset.sum_div,← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsum _) hD) (sq_nonneg _))
          (mul_nonneg hC (pow_nonneg hq _))
  let K := 64*D*C₀*E/H^2*q^N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs := (geometric_moment_summable hq hq1).mul_left K
  calc
    _ ≤ P (⋃ j : ℕ, ⋃ i : I (N+j), event j i) := measure_mono hcover
    _ ≤ ∑' j : ℕ, P (⋃ i : I (N+j), event j i) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (D*E/(jumpSize H j)^2*(C₀*q^(N+j))) := ENNReal.tsum_le_tsum hlevel
    _ = ∑' j : ℕ, ENNReal.ofReal (K*((((j:ℝ)+1)*((j:ℝ)+2))^2*q^j)) := by
      apply tsum_congr
      intro j
      rw [jump_energy_scale hH.ne']
    _ = ENNReal.ofReal (∑' j : ℕ, K*((((j:ℝ)+1)*((j:ℝ)+2))^2*q^j)) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs
    _ = _ := by rw [tsum_mul_left]

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

theorem strip_rectangle_hitting_discrete {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi)
    (hmean : stripMean H q r Fbar Q ≤ H/2) (N : ℕ)
    (hN : 3*rectCoefficient Q*(N:ℝ)*stripEnergy H q r Fbar Q ≤ (H/4)^2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Ξ : Ω → Set (ℝ × ℝ))
    {C₀ ρ : ℝ} (hC : 0 ≤ C₀) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hhit : ∀ n i, P {ω | ∃ x ∈ Ξ ω, x ∈ (dyadicRect Q n i).closed} ≤
      ENNReal.ofReal (C₀*ρ^n)) :
    P {ω | ∃ x ∈ Ξ ω, x ∈ Q.closed ∧
      stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I) = H} ≤
      ENNReal.ofReal ((64*rectCoefficient Q*C₀*stripEnergy H q r Fbar Q/H^2*ρ^N)*
        ∑' j : ℕ, (((j:ℝ)+1)*((j:ℝ)+2))^2*ρ^j) := by
  let means := fun n i => stripMean H q r Fbar (dyadicRect Q n i)
  let energy := fun n i => stripEnergy H q r Fbar (dyadicRect Q n i)
  let value := fun x : Q.closed => stripPotential H q r Fbar ((x.val.1:ℂ)+(x.val.2:ℂ)*Complex.I)
  let branch := fun x : Q.closed => dPointBranch Q x.val
  let Ξ' := fun ω => {x : Q.closed | x.val ∈ Ξ ω}
  have hroot (i : DIndex N) : means N i ≤ 3*H/4 := by
    have hb := (strip_dyadic_mean_critical hF hinj hext hcont hH hr Q hlo hhi N i).trans hN
    have hd := le_of_sq_le_sq hb (show 0 ≤ H/4 by positivity)
    dsimp only [means]
    linarith
  have hstep (n : ℕ) (i : DIndex (n+1)) :
      |means (n+1) i-means n (dParent n i)|^2 ≤ rectCoefficient Q*energy n (dParent n i) := by
    rw [sq_abs]
    exact strip_dyadic_mean_step hF hinj hext hcont hH hr Q hlo hhi n i
  have hlim (x : Q.closed) : Tendsto (fun n => means n (branch x n)) atTop (𝓝 (value x)) :=
    strip_dyadic_mean_limit hcont hH.le hr Q hlo hhi x.property
  have hnon (n : ℕ) (i : DIndex n) : 0 ≤ energy n i := integral_nonneg (fun _ => sq_nonneg _)
  have hE : 0 ≤ stripEnergy H q r Fbar Q := integral_nonneg (fun _ => sq_nonneg _)
  have hsum (n : ℕ) : ∑ i, energy n i ≤ stripEnergy H q r Fbar Q := by
    apply le_of_eq
    exact dyadic_integral_sum Q (strip_gradient_rect_memLp hF hinj hext hH hr q Q.a Q.b hlo hhi).integrable_sq n
  have hh (n : ℕ) (i : DIndex n) : P {ω | ∃ x ∈ Ξ' ω, branch x n = i} ≤ ENNReal.ofReal (C₀*ρ^n) := by
    refine (measure_mono ?_).trans (hhit n i)
    rintro ω ⟨x,hx,hi⟩
    have hxmem := dPointBranch_mem x.property n
    change x.val ∈ (dyadicRect Q n (branch x n)).closed at hxmem
    rw [hi] at hxmem
    exact ⟨x.val,hx,hxmem⟩
  have ht := dyadic_energy_hitting dParent branch means energy value hH (rectCoefficient_pos Q).le hE
    hC hρ hρ1 N (fun x n => dPointBranch_parent Q x.val n) hroot hstep hlim hnon hsum P Ξ' hh
  refine (measure_mono ?_).trans ht
  rintro ω ⟨x,hx,hxQ,hvalue⟩
  exact ⟨⟨x,hxQ⟩,hx,hvalue⟩

lemma geometric_floor_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (x : ℝ) :
    ρ^Nat.floor x ≤ Real.exp (Real.log ρ*x)/ρ := by
  have hh := Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le (Nat.sub_one_lt_floor x).le
  rw [Real.rpow_natCast] at hh
  refine hh.trans_eq ?_
  rw [Real.rpow_sub hρ,Real.rpow_one,Real.rpow_def_of_pos hρ]

lemma critical_floor {D E H : ℝ} (hD : 0 < D) (hE : 0 < E) :
    3*D*(Nat.floor (H^2/(48*D*E)):ℝ)*E ≤ (H/4)^2 := by
  have hf := Nat.floor_le (show 0 ≤ H^2/(48*D*E) by positivity)
  calc
    _ ≤ 3*D*(H^2/(48*D*E))*E := by gcongr
    _ = _ := by field_simp; ring

theorem strip_rectangle_hitting {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi)
    (hmean : stripMean H q r Fbar Q ≤ H/2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Ξ : Ω → Set (ℝ × ℝ))
    {C₀ ρ : ℝ} (hC : 0 ≤ C₀) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hhit : ∀ n i, P {ω | ∃ x ∈ Ξ ω, x ∈ (dyadicRect Q n i).closed} ≤
      ENNReal.ofReal (C₀*ρ^n)) :
    let D := rectCoefficient Q
    let E := stripEnergy H q r Fbar Q
    let T := ∑' j : ℕ, (((j:ℝ)+1)*((j:ℝ)+2))^2*ρ^j
    P {ω | ∃ x ∈ Ξ ω, x ∈ Q.closed ∧
      stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I) = H} ≤
      ENNReal.ofReal ((64*D*(C₀+1)*(T+1)/ρ)*(E/H^2)*
        Real.exp (-((-Real.log ρ)/(48*D))*H^2/E)) := by
  dsimp only
  let D := rectCoefficient Q
  let E := stripEnergy H q r Fbar Q
  let T := ∑' j : ℕ, (((j:ℝ)+1)*((j:ℝ)+2))^2*ρ^j
  have hD : 0 < D := rectCoefficient_pos Q
  have hE0 : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hT : 0 ≤ T := tsum_nonneg (fun j => mul_nonneg (sq_nonneg _) (pow_nonneg hρ.le _))
  by_cases hE : E = 0
  · have ht := strip_rectangle_hitting_discrete hF hinj hext hcont hH hr q Q hlo hhi hmean 0
      (by simp; positivity) P Ξ hC hρ.le hρ1 hhit
    change P _ ≤ ENNReal.ofReal ((64*D*C₀*E/H^2*ρ^0)*T) at ht
    change P _ ≤ ENNReal.ofReal ((64*D*(C₀+1)*(T+1)/ρ)*(E/H^2)*_)
    simpa only [hE,mul_zero,zero_div,zero_mul,ENNReal.ofReal_zero] using ht
  · have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hE)
    let x := H^2/(48*D*E)
    have ht := strip_rectangle_hitting_discrete hF hinj hext hcont hH hr q Q hlo hhi hmean (Nat.floor x)
      (critical_floor hD hEpos) P Ξ hC hρ.le hρ1 hhit
    refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
    change (64*D*C₀*E/H^2*ρ^Nat.floor x)*T ≤
      (64*D*(C₀+1)*(T+1)/ρ)*(E/H^2)*Real.exp (-((-Real.log ρ)/(48*D))*H^2/E)
    have hexp : Real.log ρ*x = -((-Real.log ρ)/(48*D))*H^2/E := by dsimp [x]; ring
    have hg := geometric_floor_bound hρ hρ1 x
    rw [hexp] at hg
    have hcoef : C₀*T ≤ (C₀+1)*(T+1) := by nlinarith
    calc
      _ ≤ (64*D*C₀*E/H^2*(Real.exp (-((-Real.log ρ)/(48*D))*H^2/E)/ρ))*T := by gcongr
      _ = (64*D/ρ)*(E/H^2)*Real.exp (-((-Real.log ρ)/(48*D))*H^2/E)*(C₀*T) := by ring
      _ ≤ (64*D/ρ)*(E/H^2)*Real.exp (-((-Real.log ρ)/(48*D))*H^2/E)*((C₀+1)*(T+1)) := by
        exact mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = _ := by ring

def localizationMeanConstant : ℝ := slabMeanCoefficient+Real.pi+1

lemma localizationMeanConstant_pos : 0 < localizationMeanConstant := by
  unfold localizationMeanConstant
  linarith [slabMeanCoefficient_pos,Real.pi_pos]

def localizationStripWidth : ℝ := 1/(32*Real.pi*localizationMeanConstant)

lemma localizationStripWidth_pos : 0 < localizationStripWidth := by
  unfold localizationStripWidth
  have hk := localizationMeanConstant_pos
  positivity

end SLEExactGauge.RectangleEnergy

end

end

end OAI
