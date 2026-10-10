import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ConformalFlow

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
namespace ExactSLEGreen
open ExactSLEMain
noncomputable def cutoffDrift (a ε : ℝ) (v : State) : State :=
  (cutoffVector a ε v.1, (-(a : ℂ) * (cutoffVector 1 ε v.1)^2).re)

lemma cutoffDrift_second_bound (a ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖(-(a : ℂ) * (cutoffVector 1 ε z)^2).re‖ ≤ |a|/ε^2 := by
  calc
    _ ≤ ‖-(a : ℂ) * (cutoffVector 1 ε z)^2‖ := Complex.abs_re_le_norm _
    _ = |a| * ‖cutoffVector 1 ε z‖^2 := by simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_pow]
    _ ≤ |a| * (1/ε)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa using cutoffVector_bound 1 ε hε z) 2) (abs_nonneg _)
    _ = _ := by ring

lemma cutoffDrift_second_lipschitz (a ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨4*|a|/ε^3,by positivity⟩
      (fun z : ℂ => (-(a : ℂ) * (cutoffVector 1 ε z)^2).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq,dist_eq_norm,← Complex.sub_re]
  have hb (u : ℂ) : ‖cutoffVector 1 ε u‖ ≤ 1/ε := by simpa using cutoffVector_bound 1 ε hε u
  have hd : ‖cutoffVector 1 ε z - cutoffVector 1 ε w‖ ≤ (2/ε^2)*‖z-w‖ := by
    have h := (cutoffVector_lipschitz 1 ε hε).dist_le_mul z w
    simp only [dist_eq_norm] at h
    change ‖cutoffVector 1 ε z - cutoffVector 1 ε w‖ ≤ (2*|1|/ε^2)*‖z-w‖ at h
    simpa only [abs_one,mul_one] using h
  have he : -(a : ℂ) * (cutoffVector 1 ε z)^2 - -(a : ℂ) * (cutoffVector 1 ε w)^2 =
      -(a : ℂ) * (cutoffVector 1 ε z - cutoffVector 1 ε w) *
        (cutoffVector 1 ε z + cutoffVector 1 ε w) := by ring
  calc
    _ ≤ ‖-(a : ℂ) * (cutoffVector 1 ε z)^2 - -(a : ℂ) * (cutoffVector 1 ε w)^2‖ := Complex.abs_re_le_norm _
    _ = |a| * ‖cutoffVector 1 ε z - cutoffVector 1 ε w‖ *
        ‖cutoffVector 1 ε z + cutoffVector 1 ε w‖ := by rw [he]; simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ (|a| * ((2/ε^2)*‖z-w‖)) * (1/ε+1/ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
        ((norm_add_le _ _).trans (add_le_add (hb z) (hb w))) (norm_nonneg _) (by positivity)
    _ = _ := by change _ = (4*|a|/ε^3)*‖z-w‖; field_simp; ring

lemma cutoffDrift_bound (a ε : ℝ) (hε : 0 < ε) (v : State) :
    ‖cutoffDrift a ε v‖ ≤ max (|a|/ε) (|a|/ε^2) := by
  exact max_le_max (cutoffVector_bound a ε hε v.1) (cutoffDrift_second_bound a ε hε v.1)

lemma cutoffDrift_lipschitz (a ε : ℝ) (hε : 0 < ε) :
    LipschitzWith (max ⟨2*|a|/ε^2,by positivity⟩ ⟨4*|a|/ε^3,by positivity⟩)
      (cutoffDrift a ε) := by
  convert ((cutoffVector_lipschitz a ε hε).prodMk (cutoffDrift_second_lipschitz a ε hε)).comp LipschitzWith.prod_fst using 1 <;> first | rfl | simp only [mul_one]

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEMain

lemma cutoffDrift_eq_physical (a ε : ℝ) (v : State) (hy : ε ≤ v.1.im) :
    cutoffDrift a ε v = ((a : ℂ)/v.1, (-(a : ℂ)/v.1^2).re) := by
  simp only [cutoffDrift,cutoffVector,heightClamp_eq hy,Complex.ofReal_one,one_div]
  congr 1
  rw [inv_pow,div_eq_mul_inv]

 

theorem state_eq_loewner_on_safe
    (a ε : ℝ) (hε : 0 < ε) (b : ℝ≥0 → ℝ) (hb : Continuous b) (_hb0 : b 0 = 0)
    (z : ℂ) (V : ℝ≥0 → State) (hVc : Continuous V)
    (hVe : ∀ t, V t = (z,0) + b t • ((-1 : ℂ), (0 : ℝ)) +
      ∫ u in (0 : ℝ)..(t : ℝ), cutoffDrift a ε (V u.toNNReal))
    (T : ℝ≥0) (hy : ∀ t ≤ T, ε ≤ (V t).1.im) :
    alive a b T z ∧
      (∀ t ≤ T, loewnerMap a b t z - (b t : ℂ) = (V t).1) ∧
      Real.log ‖deriv (loewnerMap a b T) z‖ = (V T).2 := by
  have hAc := (cutoffDrift_lipschitz a ε hε).continuous
  have hIc (t : ℝ≥0) : IntervalIntegrable
      (fun u : ℝ => cutoffDrift a ε (V u.toNNReal)) volume 0 t :=
    (hAc.comp (hVc.comp continuous_real_toNNReal)).intervalIntegrable 0 t
  have hfst (t : ℝ≥0) : (V t).1 = z - (b t : ℂ) +
      ∫ u in (0 : ℝ)..(t : ℝ), cutoffVector a ε (V u.toNNReal).1 := by
    have h := congrArg Prod.fst (hVe t)
    have hi := (ContinuousLinearMap.fst ℝ ℂ ℝ).intervalIntegral_comp_comm (hIc t)
    simp only [Prod.fst_add] at h
    change (V t).1 = z + b t • (-1 : ℂ) +
      (ContinuousLinearMap.fst ℝ ℂ ℝ) (∫ u in (0 : ℝ)..(t : ℝ), cutoffDrift a ε (V u.toNNReal)) at h
    rw [← hi] at h
    simpa only [ContinuousLinearMap.coe_fst',Prod.fst_add,Prod.fst_smul,Complex.real_smul,Complex.ofReal_neg,
      mul_neg,mul_one,sub_eq_add_neg,cutoffDrift] using h
  have hsnd (t : ℝ≥0) : (V t).2 =
      ∫ u in (0 : ℝ)..(t : ℝ), (-(a : ℂ)*(cutoffVector 1 ε (V u.toNNReal).1)^2).re := by
    have h := congrArg Prod.snd (hVe t)
    have hi := (ContinuousLinearMap.snd ℝ ℂ ℝ).intervalIntegral_comp_comm (hIc t)
    simp only [Prod.snd_add] at h
    change (V t).2 = (0 : ℝ) + b t • (0 : ℝ) +
      (ContinuousLinearMap.snd ℝ ℂ ℝ) (∫ u in (0 : ℝ)..(t : ℝ), cutoffDrift a ε (V u.toNNReal)) at h
    rw [← hi] at h
    simpa only [ContinuousLinearMap.coe_snd',Prod.snd_add,Prod.snd_smul,smul_zero,add_zero,zero_add,cutoffDrift] using h
  let G : ℝ≥0 → ℂ := fun t => (V t).1 + (b t : ℂ)
  have hGc : Continuous G := hVc.fst.add (Complex.continuous_ofReal.comp hb)
  have hGe (t : ℝ≥0) : G t = z + ∫ u in (0 : ℝ)..(t : ℝ),
      cutoffVector a ε (G u.toNNReal + -(b u.toNNReal : ℂ)) := by
    simp only [G,add_neg_cancel_right]
    rw [hfst t]
    abel
  have hG0 : G 0 = z := by simpa using hGe 0
  have hode : odeUntil a b z T (fun u : ℝ => G u.toNNReal) := by
    refine ⟨by simpa using hG0,?_⟩
    intro u hu
    have hut : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    have huy := hy _ hut
    have hd := ExactSLEFlow.integral_flow_hasDerivWithinAt
      (cutoffVector_lipschitz a ε hε).continuous (Complex.continuous_ofReal.comp hb).neg
      hGc hGe T u hu
    have hGim : (G u.toNNReal).im = (V u.toNNReal).1.im := by simp [G]
    refine ⟨by rw [hGim]; exact hε.trans_le huy,?_⟩
    simpa only [Function.comp_def,Pi.neg_apply,cutoffVector,G,add_neg_cancel_right,heightClamp_eq huy,sub_eq_add_neg] using hd
  have hlo (t : ℝ≥0) (ht : t ≤ T) : loewnerMap a b t z - (b t : ℂ) = (V t).1 := by
    rw [loewnerMap_eq (odeUntil_mono hode ht)]
    simp only [Real.toNNReal_coe,G,add_sub_cancel_right]
  refine ⟨⟨_,hode⟩,hlo,?_⟩
  rw [log_norm_deriv_loewnerMap hb ⟨_,hode⟩, hsnd T]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le T.coe_nonneg] using hu
  have hut : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu'.2).trans_eq (by simp)
  dsimp only
  rw [hlo _ hut,cutoffVector,heightClamp_eq (hy _ hut)]
  simp only [Complex.ofReal_one,inv_pow,div_eq_mul_inv,one_mul]

end ExactSLEGreen

namespace ExactSLEHitting
variable {Ω : Type*} {m : MeasurableSpace Ω}
variable (ℱ : Filtration ℝ≥0 m) (f : ℝ≥0 → Ω → ℝ)

lemma firstContact_mem (hc : ∀ ω, Continuous (fun t => f t ω)) (ω : Ω)
    (hex : ∃ t, f t ω ≤ 0) :
    f (hittingAfter f (Iic 0) 0 ω).untopA ω ≤ 0 := by
  have he : ∃ t : ℝ≥0, 0 ≤ t ∧ f t ω ∈ Iic 0 := by
    obtain ⟨t,ht⟩ := hex
    exact ⟨t,bot_le,ht⟩
  rw [hittingAfter,ite_eq_left he]
  change f (sInf {t : ℝ≥0 | 0 ≤ t ∧ f t ω ≤ 0}) ω ≤ 0
  have hcl : IsClosed {t : ℝ≥0 | 0 ≤ t ∧ f t ω ≤ 0} :=
    isClosed_Ici.inter (isClosed_le (hc ω) continuous_const)
  exact (hcl.csInf_mem he ⟨0,fun _ _ => bot_le⟩).2

lemma firstContact_le_iff (hc : ∀ ω, Continuous (fun t => f t ω))
    (ω : Ω) (t : ℝ≥0) :
    hittingAfter f (Iic 0) 0 ω ≤ t ↔ ∃ u ≤ t, f u ω ≤ 0 := by
  constructor
  · intro h
    have hex : ∃ u, f u ω ≤ 0 := by
      by_contra hn
      have hz : hittingAfter f (Iic 0) 0 ω = ⊤ := by
        rw [hittingAfter_eq_top_iff]
        intro j _ hj
        exact hn ⟨j,hj⟩
      rw [hz] at h
      exact WithTop.not_top_le_coe t h
    refine ⟨(hittingAfter f (Iic 0) 0 ω).untopA,?_, firstContact_mem f hc ω hex⟩
    exact WithTop.untopA_le h
  · rintro ⟨u,hu,hfu⟩
    exact (hittingAfter_le_of_mem (by exact bot_le) hfu).trans (WithTop.coe_le_coe.mpr hu)

lemma measurable_has_contact (hc : ∀ ω, Continuous (fun t => f t ω))
    (hm : ∀ t, Measurable[ℱ t] (f t)) (t : ℝ≥0) :
    MeasurableSet[ℱ t] {ω | ∃ u ≤ t, f u ω ≤ 0} := by
  let g : Icc (0 : ℝ≥0) t → Ω → ℝ≥0∞ := fun u ω => ENNReal.ofReal (f u ω)
  have hg : @Measurable Ω ℝ≥0∞ (ℱ t) _ (⨅ u, g u) := by
    apply measurable_iInf_of_upperSemicontinuous
    · intro u
      exact ((hm u).mono (ℱ.mono u.2.2) le_rfl).ennreal_ofReal
    · intro ω
      exact (ENNReal.continuous_ofReal.comp ((hc ω).comp continuous_subtype_val)).upperSemicontinuous
  have he : {ω | ∃ u ≤ t, f u ω ≤ 0} = {ω | (⨅ u, g u) ω = 0} := by
    ext ω
    simp only [mem_ofPred_eq,iInf_apply]
    constructor
    · rintro ⟨u,hu,hfu⟩
      apply le_antisymm _ bot_le
      exact (iInf_le (fun u => g u ω) ⟨u,bot_le,hu⟩).trans (by change ENNReal.ofReal (f u ω) ≤ 0; exact le_of_eq (ENNReal.ofReal_eq_zero.mpr hfu))
    · intro h
      obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ t from bot_le)) (hc ω).continuousOn
      refine ⟨u,hu.2,?_⟩
      have hl : ENNReal.ofReal (f u ω) ≤ ⨅ v, g v ω := by
        apply le_iInf
        intro v
        exact ENNReal.ofReal_le_ofReal (hmin v.2)
      rw [h] at hl
      exact ENNReal.ofReal_eq_zero.mp (le_antisymm hl bot_le)
  rw [he]
  exact measurableSet_eq_fun hg measurable_const

lemma firstContact_stopping (hc : ∀ ω, Continuous (fun t => f t ω))
    (hm : ∀ t, Measurable[ℱ t] (f t)) :
    IsStoppingTime ℱ (hittingAfter f (Iic 0) 0) := by
  intro t
  have he : {ω | hittingAfter f (Iic 0) 0 ω ≤ t} = {ω | ∃ u ≤ t, f u ω ≤ 0} := by
    ext ω
    exact firstContact_le_iff f hc ω t
  rw [he]
  exact measurable_has_contact ℱ f hc hm t

end ExactSLEHitting

namespace ExactSLEHitting
variable {Ω : Type*} {m : MeasurableSpace Ω}
variable (ℱ : Filtration ℝ≥0 m) (f : ℝ≥0 → Ω → ℝ)

lemma boundedContact_le_iff (hc : ∀ ω, Continuous (fun t => f t ω))
    (ω : Ω) (B t : ℝ≥0) (ht : t < B) :
    hittingBtwn f (Iic 0) 0 B ω ≤ t ↔ ∃ u ≤ t, f u ω ≤ 0 := by
  constructor
  · intro h
    have hex : ∃ u ∈ Icc (0 : ℝ≥0) B, f u ω ∈ Iic 0 := by
      by_contra hn
      have he : hittingBtwn f (Iic 0) 0 B ω = B := by simp only [hittingBtwn,ite_eq_right hn]
      rw [he] at h
      exact not_le.mpr ht h
    have hcl : IsClosed (Icc (0 : ℝ≥0) B ∩ {u | f u ω ∈ Iic 0}) :=
      isClosed_Icc.inter (isClosed_Iic.preimage (hc ω))
    have hmem : f (hittingBtwn f (Iic 0) 0 B ω) ω ≤ 0 := by
      rw [hittingBtwn,ite_eq_left hex]
      exact (hcl.csInf_mem hex bddBelow_Icc.inter_of_left).2
    exact ⟨_,h,hmem⟩
  · rintro ⟨u,hu,hfu⟩
    exact (hittingBtwn_le_of_mem bot_le (hu.trans ht.le) hfu).trans hu

lemma boundedContact_stopping (hc : ∀ ω, Continuous (fun t => f t ω))
    (hm : ∀ t, Measurable[ℱ t] (f t)) (B : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => ((hittingBtwn f (Iic (0 : ℝ)) (0 : ℝ≥0) B ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases ht : t < B
  · have he : {ω | ((hittingBtwn f (Iic (0 : ℝ)) (0 : ℝ≥0) B ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | ∃ u ≤ t, f u ω ≤ 0} := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe]
      exact boundedContact_le_iff f hc ω B t ht
    rw [he]
    exact measurable_has_contact ℱ f hc hm t
  · have he : {ω | ((hittingBtwn f (Iic (0 : ℝ)) (0 : ℝ≥0) B ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
      apply eq_univ_of_forall
      intro ω
      exact WithTop.coe_le_coe.mpr ((hittingBtwn_le ω).trans (le_of_not_gt ht))
    rw [he]
    exact MeasurableSet.univ

lemma nonneg_before_boundedContact (hc : ∀ ω, Continuous (fun t => f t ω))
    (h0 : ∀ ω, 0 ≤ f 0 ω) (B : ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (ht : t ≤ hittingBtwn f (Iic 0) 0 B ω) : 0 ≤ f t ω := by
  by_cases hz : t = 0
  · simpa only [hz] using h0 ω
  · have ht0 : 0 < t := bot_lt_iff_ne_bot.mpr hz
    have : NeBot (𝓝[<] t) := nhdsWithin_Iio_neBot' ⟨0,ht0⟩ le_rfl
    apply ge_of_tendsto ((hc ω).continuousAt.tendsto.mono_left (show 𝓝[<] t ≤ 𝓝 t from inf_le_left))
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hn : f u ω ∉ Iic 0 := notMem_of_lt_hittingBtwn (hu.trans_le ht) bot_le
    exact le_of_lt (lt_of_not_ge hn)

lemma boundedContact_eq_zero (hc : ∀ ω, Continuous (fun t => f t ω))
    (h0 : ∀ ω, 0 ≤ f 0 ω) (B : ℝ≥0) (ω : Ω)
    (ht : hittingBtwn f (Iic 0) 0 B ω < B) :
    f (hittingBtwn f (Iic 0) 0 B ω) ω = 0 := by
  apply le_antisymm _ (nonneg_before_boundedContact f hc h0 B ω _ le_rfl)
  obtain ⟨u,hu,hfu⟩ := (boundedContact_le_iff f hc ω B _ ht).mp le_rfl
  have he : hittingBtwn f (Iic 0) 0 B ω = u :=
    le_antisymm (hittingBtwn_le_of_mem bot_le (hu.trans ht.le) hfu) hu
  simpa only [he] using hfu

end ExactSLEHitting

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

noncomputable def physicalRadius (v : State) : ℝ := Y v * Real.exp (-J v)
lemma physicalRadius_continuous : Continuous physicalRadius :=
  Y.continuous.mul (Real.continuous_exp.comp J.continuous.neg)

lemma alpha_pos {a : ℝ} (ha : 1/4 < a) : 0 < alpha a := by
  have ha0 : 0 < a := by linarith
  unfold alpha
  rw [sub_pos,div_lt_one (by positivity)]
  linarith

lemma physicalGreen_bound (a ρ : ℝ) (ha : 1/4 < a) (hρ : 0 < ρ)
    (v : State) (hy : 0 < Y v) (hr : ρ ≤ physicalRadius v) :
    physicalGreen a v ≤ Real.exp (-alpha a * Real.log ρ) := by
  have hq := Q_pos hy
  have hlq : 2*Real.log (Y v) ≤ Real.log (Q v) := by
    have he := Real.log_pow (Y v) 2
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    apply Real.log_le_log (by positivity)
    dsimp only [Q]
    nlinarith [sq_nonneg (X v)]
  have hlr : Real.log ρ ≤ Real.log (Y v) - J v := by
    have h := Real.log_le_log hρ hr
    simpa only [physicalRadius,Real.log_mul hy.ne' (Real.exp_ne_zero _),Real.log_exp,sub_eq_add_neg] using h
  have hp : 0 ≤ p a / 2 := by unfold p; linarith
  have ha' := alpha_pos ha
  apply Real.exp_le_exp.mpr
  unfold logGreen
  nlinarith [mul_le_mul_of_nonneg_left hlq hp,mul_le_mul_of_nonneg_left hlr ha'.le]

lemma physicalGreen_eq_radius_sine (a : ℝ) (v : State) (hy : 0 < Y v) :
    physicalGreen a v = (physicalRadius v) ^ (-alpha a) * (Y v / ‖v.1‖) ^ (p a) := by
  have hzn : 0 < ‖v.1‖ := lt_of_lt_of_le hy (Complex.im_le_norm _)
  have hr : 0 < physicalRadius v := mul_pos hy (Real.exp_pos _)
  have hqlog : Real.log (Q v) = 2*Real.log ‖v.1‖ := by
    rw [Q_eq,Complex.normSq_eq_norm_sq,Real.log_pow]
    norm_num
  rw [Real.rpow_def_of_pos hr,Real.rpow_def_of_pos (div_pos hy hzn),← Real.exp_add]
  rw [physicalRadius,Real.log_mul hy.ne' (Real.exp_ne_zero _),Real.log_exp,
    Real.log_div hy.ne' hzn.ne']
  simp only [physicalGreen,logGreen] at *
  rw [hqlog]
  congr 1
  ring

 
lemma exists_localState (a ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ∃ V : ℝ≥0 → ExactSLEGenerator.Driver → State,
      (∀ b, Continuous (fun t => V t b)) ∧
      (∀ t, Measurable[rawFiltration t] (V t)) ∧
      (∀ b, V 0 b = (z,0)) ∧
      (∀ (s h : ℝ≥0) b, V (s+h) b = V s b + increment s h b • noise +
        ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), cutoffDrift a ε (V t.toNNReal b)) := by
  exact exists_adapted_additive_brownian (cutoffDrift a ε)
    ⟨max (|a|/ε) (|a|/ε^2),by positivity⟩ _
    (cutoffDrift_lipschitz a ε hε) (cutoffDrift_bound a ε hε) (z,0) noise

noncomputable def localState (a ε : ℝ) (hε : 0 < ε) (z : ℂ) : ℝ≥0 → ExactSLEGenerator.Driver → State :=
  Classical.choose (exists_localState a ε hε z)
lemma localState_continuous (a ε : ℝ) (hε : 0 < ε) (z : ℂ) (b : ExactSLEGenerator.Driver) :
    Continuous (fun t => localState a ε hε z t b) :=
  (Classical.choose_spec (exists_localState a ε hε z)).1 b
lemma localState_adapted (a ε : ℝ) (hε : 0 < ε) (z : ℂ) (t : ℝ≥0) :
    Measurable[rawFiltration t] (localState a ε hε z t) :=
  (Classical.choose_spec (exists_localState a ε hε z)).2.1 t
lemma localState_zero (a ε : ℝ) (hε : 0 < ε) (z : ℂ) (b : ExactSLEGenerator.Driver) :
    localState a ε hε z 0 b = (z,0) :=
  (Classical.choose_spec (exists_localState a ε hε z)).2.2.1 b
lemma localState_eq (a ε : ℝ) (hε : 0 < ε) (z : ℂ) (s h : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    localState a ε hε z (s+h) b = localState a ε hε z s b + increment s h b • noise +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), cutoffDrift a ε (localState a ε hε z t.toNNReal b) :=
  (Classical.choose_spec (exists_localState a ε hε z)).2.2.2 s h b
lemma localState_eq_zero (a ε : ℝ) (hε : 0 < ε) (z : ℂ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    localState a ε hε z t b = (z,0) + b.1 t • noise +
      ∫ u in (0 : ℝ)..(t : ℝ), cutoffDrift a ε (localState a ε hε z u.toNNReal b) := by
  simpa only [zero_add,localState_zero,increment,b.2,sub_zero,NNReal.coe_zero]
    using localState_eq a ε hε z 0 t b

 

theorem localGreen_optional (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a ε : ℝ) (ha : a ≠ 0) (hε : 0 < ε) (z : ℂ) (N B : ℝ≥0)
    (S T : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b ≤ T b) (hTB : ∀ b, T b ≤ B)
    (hsafe : ∀ b t, t ≤ T b → ε ≤ Y (localState a ε hε z t b) ∧
      ‖localState a ε hε z t b‖ ≤ N)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    ∫ b in U, physicalGreen a (localState a ε hε z (S b) b) ∂W =
      ∫ b in U, physicalGreen a (localState a ε hε z (T b) b) ∂W := by
  have hf := greenCutoff_smooth a ε hε N
  have hG (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t ≤ T b) :
      generator (greenCutoff a ε N) (cutoffDrift a ε) noise (localState a ε hε z t b) = 0 := by
    have hv := hsafe b t ht
    have hg := greenCutoff_generator_zero a ε ha hε N (localState a ε hε z t b) hv.2 hv.1
    change (1/2 : ℝ) * fderiv ℝ (fun w => fderiv ℝ (greenCutoff a ε N) w noise)
      (localState a ε hε z t b) noise + fderiv ℝ (greenCutoff a ε N)
      (localState a ε hε z t b) (cutoffDrift a ε (localState a ε hε z t b)) = 0
    rw [cutoffDrift_eq_physical a ε _ hv.1]
    exact hg
  have ho := compact_test_optional_sampling W hW (localState a ε hε z)
    (localState_continuous a ε hε z) (localState_adapted a ε hε z)
    (cutoffDrift a ε) (cutoffDrift_lipschitz a ε hε).continuous
    (max (|a|/ε) (|a|/ε^2)) (by positivity) (cutoffDrift_bound a ε hε) noise
    (by simp [noise,Prod.norm_def]) (localState_eq a ε hε z)
    (greenCutoff a ε N) hf (greenCutoff_compact a ε N) S T B hS hT hST hTB hG U hU
  have he (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t ≤ T b) :
      greenCutoff a ε N (localState a ε hε z t b) = physicalGreen a (localState a ε hε z t b) :=
    (greenCutoff_eq_near a ε hε N _ (hsafe b t ht).2 (hsafe b t ht).1).eq_of_nhds
  simpa only [he _ _ (hST _),he _ _ le_rfl] using ho

end ExactSLEGreen

namespace ExactSLEBarrier

 

structure Evolution (a : ℝ) (T : ℝ≥0) (y j q : ℝ → ℝ) : Prop where
  yc : ContinuousOn y (Icc 0 (T : ℝ))
  jc : ContinuousOn j (Icc 0 (T : ℝ))
  yp : ∀ t ∈ Icc 0 (T : ℝ), 0 < y t
  qp : ∀ t ∈ Icc 0 (T : ℝ), 0 < q t
  yd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt y (-a*y t/q t) (Icc 0 (T : ℝ)) t
  jd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt j
    (-a*(q t-2*(y t)^2)/(q t)^2) (Icc 0 (T : ℝ)) t

variable {a : ℝ} {T : ℝ≥0} {y j q : ℝ → ℝ}

lemma Evolution.logHeight_deriv (h : Evolution a T y j q) {t : ℝ}
    (ht : t ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t => Real.log (y t)) (-a/q t) (Icc 0 (T : ℝ)) t := by
  convert (h.yd t ht).log (h.yp t ht).ne' using 1
  field_simp [(h.yp t ht).ne']

lemma Evolution.logRadius_deriv (h : Evolution a T y j q) {t : ℝ}
    (ht : t ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t => Real.log (y t)-j t)
      (-2*a*(y t)^2/(q t)^2) (Icc 0 (T : ℝ)) t := by
  convert (h.logHeight_deriv ht).sub (h.jd t ht) using 1
  try rfl
  field_simp [(h.qp t ht).ne']
  ring

lemma Evolution.height_le (h : Evolution a T y j q) (ha : 0 ≤ a)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : y t ≤ y 0 := by
  have hm : AntitoneOn y (Icc 0 (T : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (T : ℝ)) h.yc
      (fun u hu => (h.yd u (interior_subset hu)).mono interior_subset)
      (fun u hu => div_nonpos_of_nonpos_of_nonneg (by nlinarith [h.yp u (interior_subset hu)])
        (h.qp u (interior_subset hu)).le)
  exact hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1

end ExactSLEBarrier
end

end OAI
