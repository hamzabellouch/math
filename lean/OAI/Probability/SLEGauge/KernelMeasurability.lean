import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ProductIntegrability

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
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEFlow
variable {Ω : Type*} [MeasurableSpace Ω]
lemma localState_parameter_measurable (a : ℝ) (ε : Ω → ℝ) (hε : ∀ ω, 0 < ε ω)
    (z : Ω → ℂ) (b : Ω → ExactSLEGenerator.Driver)
    (hεm : Measurable ε) (hzm : Measurable z) (hbm : Measurable b) (t : ℝ≥0) :
    Measurable (fun ω => localState a (ε ω) (hε ω) (z ω) t (b ω)) := by
  let A : Ω → State → State := fun ω => cutoffDrift a (ε ω)
  let L : Ω → ℝ≥0 := fun ω => ⟨max (|a|/ε ω) (|a|/(ε ω)^2), by positivity⟩
  let K : Ω → ℝ≥0 := fun ω => ⟨max (2*|a|/(ε ω)^2) (4*|a|/(ε ω)^3), by positivity⟩
  have hA : ∀ ω, LipschitzWith (K ω) (A ω) := fun ω => cutoffDrift_lipschitz a (ε ω) (hε ω)
  have hb : ∀ ω v, ‖A ω v‖ ≤ L ω := fun ω => cutoffDrift_bound a (ε ω) (hε ω)
  have hmA : Measurable (Function.uncurry A) := by
    change Measurable (fun w : Ω × State => cutoffDrift a (ε w.1) w.2)
    unfold cutoffDrift cutoffVector heightClamp
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  let u : ℝ≥0 → Ω → State := fun t ω => (b ω).1 t • noise
  have huc (ω : Ω) : Continuous (fun t => u t ω) := (b ω).1.continuous.smul continuous_const
  have hum (t : ℝ≥0) : Measurable (u t) := ((driver_eval_measurable t).measurable.comp hbm).smul_const noise
  obtain ⟨F,hFc,hFm,hFe⟩ := measurable_parameter_flow A L K hA hb hmA u huc hum
    (fun ω => (z ω,0)) (hzm.prodMk measurable_const)
  have he (ω : Ω) (t : ℝ≥0) : F t ω = localState a (ε ω) (hε ω) (z ω) t (b ω) - u t ω := by
    apply integral_flow_unique (hA ω) (huc ω) (huc ω) (hFc ω)
      ((localState_continuous a (ε ω) (hε ω) (z ω) (b ω)).sub (huc ω)) (hFe ω)
      (fun s => ?_) (T := t) (fun _ _ => rfl) le_rfl
    simp only [Pi.sub_apply,sub_add_cancel]
    rw [localState_eq_zero]
    dsimp [u,A]
    abel
  convert (hFm t).add (hum t) using 1
  funext ω
  change localState a (ε ω) (hε ω) (z ω) t (b ω) = F t ω + u t ω
  rw [he]
  simp

lemma localState_parameter_joint_measurable (a : ℝ) (ε : Ω → ℝ) (hε : ∀ ω, 0 < ε ω)
    (z : Ω → ℂ) (b : Ω → ExactSLEGenerator.Driver)
    (hεm : Measurable ε) (hzm : Measurable z) (hbm : Measurable b) :
    Measurable (fun p : ℝ≥0 × Ω => localState a (ε p.2) (hε p.2) (z p.2) p.1 (b p.2)) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (fun ω => localState_continuous a (ε ω) (hε ω) (z ω) (b ω))
    (fun t => localState_parameter_measurable a ε hε z b hεm hzm hbm t)
end ExactSLEGreen

namespace ExactSLEHitting
variable {Ω : Type*} [MeasurableSpace Ω]
lemma boundedContact_parameter_measurable (f : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => f t ω)) (hm : ∀ t, Measurable (f t))
    (B : Ω → ℝ≥0) (hB : Measurable B) :
    Measurable (fun ω => hittingBtwn f (Iic 0) 0 (B ω) ω) := by
  apply measurable_of_Iic
  intro t
  have he : (fun ω => hittingBtwn f (Iic 0) 0 (B ω) ω) ⁻¹' Iic t =
      {ω | B ω ≤ t} ∪ {ω | ∃ u ≤ t, f u ω ≤ 0} := by
    ext ω
    simp only [mem_preimage,mem_Iic,mem_union,mem_ofPred_eq]
    by_cases h : B ω ≤ t
    · exact iff_of_true ((hittingBtwn_le ω).trans h) (Or.inl h)
    · rw [or_iff_right h]
      exact boundedContact_le_iff f hc ω (B ω) t (lt_of_not_ge h)
  rw [he]
  exact (measurableSet_le hB measurable_const).union
    (measurable_has_contact (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Ω) le_rfl) f hc (fun t => hm t) t)
end ExactSLEHitting

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEHitting
variable {Ω : Type*} [MeasurableSpace Ω]
lemma regionStop_parameter_measurable (a : ℝ) (ε : Ω → ℝ) (hε : ∀ ω, 0 < ε ω)
    (z : Ω → ℂ) (b : Ω → ExactSLEGenerator.Driver) (N ρ δ : Ω → ℝ) (B : Ω → ℝ≥0)
    (hεm : Measurable ε) (hzm : Measurable z) (hbm : Measurable b)
    (hN : Measurable N) (hρ : Measurable ρ) (hδ : Measurable δ) (hB : Measurable B) :
    Measurable (fun ω => regionStop a (ε ω) (hε ω) (z ω) (N ω) (ρ ω) (δ ω) (B ω) (b ω)) := by
  apply boundedContact_parameter_measurable
    (fun t ω => regionMonitor (ε ω) (N ω) (ρ ω) (δ ω)
      (localState a (ε ω) (hε ω) (z ω) t (b ω)))
    (fun ω => (regionMonitor_continuous _ _ _ _).comp (localState_continuous _ _ _ _ _)) _ B hB
  intro t
  have hv := localState_parameter_measurable a ε hε z b hεm hzm hbm t
  have hy : Measurable (fun ω => Y (localState a (ε ω) (hε ω) (z ω) t (b ω))) :=
    Y.continuous.measurable.comp hv
  have hr : Measurable (fun ω => physicalRadius (localState a (ε ω) (hε ω) (z ω) t (b ω))) :=
    physicalRadius_continuous.measurable.comp hv
  unfold regionMonitor
  exact (hy.sub hεm).min ((hN.sub hv.norm).min ((hr.sub hρ).min (hy.sub (hδ.mul hv.fst.norm))))
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
noncomputable def explicitRadialLocalization (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (hδ : 0 < δ)
    (hs : δ*‖z‖ ≤ z.im) : RadialLocalization a z ρ δ := by
  let m := heightFloor z.im ρ δ
  let C := logCeiling z.im ρ δ
  have hm : 0 < m := heightFloor_pos _ _ _
  have hC : 0 ≤ C := logCeiling_nonneg _ _ _
  have hmz : m ≤ z.im := heightFloor_le hz hρ hr
  let N : ℝ≥0 := ⟨z.im/δ+C+1,by positivity⟩
  let B : ℝ≥0 := ⟨z.im^2/(2*a*δ^2)+1,by positivity⟩
  have hinit : 0 ≤ regionMonitor (m/2) N ρ δ (z,0) := by
    apply (regionMonitor_nonneg_iff _ _ _ _ _).mpr
    have hnorm : ‖z‖ ≤ z.im/δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hs)
    refine ⟨?_,?_,?_,hs⟩
    · change m/2 ≤ z.im
      linarith
    · simpa only [Prod.norm_def,Real.norm_eq_abs,abs_zero,max_eq_left (norm_nonneg z)] using
        (show ‖z‖ ≤ (N : ℝ) by change ‖z‖ ≤ z.im/δ+C+1; linarith)
    · simpa only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one] using hr
  refine ⟨m/2,by positivity,N,B,hinit,by change m/2 < m; linarith,?_,?_⟩
  · change z.im/δ+C < z.im/δ+C+1
    linarith
  · change z.im^2 < 2*a*δ^2*(z.im^2/(2*a*δ^2)+1)
    have hp : 0 < 2*a*δ^2 := by positivity
    field_simp
    nlinarith

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
lemma localizationApproximation_tendsto (a : ℝ) (ha : 1/4 < a) (ha0 : 0 < a)
    (z : ℂ) (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (_hr : ρ ≤ z.im)
    (b : ExactSLEGenerator.Driver)
    (L : ∀ n, RadialLocalization a z ρ (angleThreshold z n)) :
    Tendsto (fun n => physicalGreen a (localState a (L n).ε (L n).hε z
      (regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b) b)) atTop
      (𝓝 (radialWeight a b.1 z ρ)) := by
  classical
  let T (n : ℕ) := regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b
  let V (n : ℕ) := localState a (L n).ε (L n).hε z (T n) b
  have hexit (n : ℕ) : physicalRadius (V n) = ρ ∨ Y (V n) = angleThreshold z n*‖(V n).1‖ :=
    regionStop_true_exit a (L n).ε ha0 (L n).hε z (L n).N ρ (angleThreshold z n)
      hρ (angleThreshold_pos z hz n) (L n).B (L n).initial (L n).small (L n).large (L n).time b
  have hactual (n : ℕ) : alive a b.1 (T n) z ∧ actualState a b.1 (T n) z = V n :=
    regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b _ le_rfl
  by_cases hex : ∃ t : ℝ≥0, alive a b.1 t z ∧ physicalRadius (actualState a b.1 t z) = ρ
  · obtain ⟨t,ht,htr⟩ := hex
    obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht
    have he : ∀ᶠ n in atTop, physicalGreen a (localState a (L n).ε (L n).hε z
      (regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b) b) = radialWeight a b.1 z ρ := by
      filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
      have ht' : T n ≤ t := regionStop_le_hit a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
        (L n).B (L n).initial b t htr
      have hη' := hηs (T n) ht'
      rw [(hactual n).2] at hη'
      rcases hexit n with hR|hS
      · exact regionStop_weight_eq a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b hR
      · have hsafe := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b (T n) le_rfl
        have hnp : 0 < ‖(V n).1‖ := ((L n).hε.trans_le hsafe.1).trans_le (Complex.im_le_norm _)
        have hd : Y (V n)/‖(V n).1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
        rw [hd] at hη'
        exact False.elim (not_le.mpr hn hη')
    exact Filter.Tendsto.congr' (he.mono fun n hn => hn.symm) tendsto_const_nhds
  · have hw : radialWeight a b.1 z ρ = 0 := by rw [radialWeight,ite_eq_left (radialTime_top_of_no_hit a b.1 z ρ hex)]
    rw [hw]
    have hbound (n : ℕ) : physicalGreen a (localState a (L n).ε (L n).hε z
      (regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b) b) ≤
        Real.exp (-alpha a*Real.log ρ) * (angleThreshold z n)^(p a) := by
      rcases hexit n with hR|hS
      · exact False.elim (hex ⟨T n,(hactual n).1,by simpa only [(hactual n).2] using hR⟩)
      · have hs := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b (T n) le_rfl
        exact physicalGreen_angle_bound a ρ (angleThreshold z n) ha hρ (V n)
          ((L n).hε.trans_le hs.1) hs.2.2.1 hS
    have hp : 0 < p a := by unfold p; linarith
    have hu : Tendsto (fun n => Real.exp (-alpha a*Real.log ρ) * (angleThreshold z n)^(p a)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ((angleThreshold_tendsto z).rpow_const_nhds_zero hp).const_mul
        (Real.exp (-alpha a*Real.log ρ))
    exact squeeze_zero (fun n => (Real.exp_pos _).le) hbound hu

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

theorem joint_radialWeight_measurable (a : ℝ) (ha : 1/4 < a) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    Measurable (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im} =>
      radialWeight a p.1.1 p.2.1 (p.2.1.im*q)) := by
  have ha0 : 0<a := by linarith
  let Ω := ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im}
  let z : Ω → ℂ := fun p => p.2.1
  let b : Ω → ExactSLEGenerator.Driver := Prod.fst
  have hz (ω : Ω) : 0<(z ω).im := ω.2.2
  have hzM : Measurable z := measurable_subtype_coe.comp measurable_snd
  have hbM : Measurable b := measurable_fst
  let ρ : Ω → ℝ := fun ω => (z ω).im*q
  have hρ (ω : Ω) : 0<ρ ω := mul_pos (hz ω) hq
  have hr (ω : Ω) : ρ ω≤(z ω).im := mul_le_of_le_one_right (hz ω).le hq1
  let δ : ℕ → Ω → ℝ := fun n ω => angleThreshold (z ω) n
  let L (n : ℕ) (ω : Ω) := explicitRadialLocalization a ha0 (z ω) (hz ω) (ρ ω) (δ n ω)
    (hρ ω) (hr ω) (angleThreshold_pos (z ω) (hz ω) n) (angleThreshold_initial (z ω) (hz ω) n)
  have hρM : Measurable ρ := hzM.im.mul_const q
  have hδM (n : ℕ) : Measurable (δ n) := by
    dsimp [δ,angleThreshold]
    exact (hzM.im.div hzM.norm).div_const _
  have hεM (n : ℕ) : Measurable (fun ω => (L n ω).ε) := by
    change Measurable (fun ω => heightFloor (z ω).im (ρ ω) (δ n ω)/2)
    unfold heightFloor
    fun_prop
  have hNM (n : ℕ) : Measurable (fun ω => (L n ω).N) := by
    change Measurable (fun ω => (⟨(z ω).im/δ n ω+logCeiling (z ω).im (ρ ω) (δ n ω)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    unfold logCeiling heightFloor
    fun_prop
  have hBM (n : ℕ) : Measurable (fun ω => (L n ω).B) := by
    change Measurable (fun ω => (⟨(z ω).im^2/(2*a*(δ n ω)^2)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    fun_prop
  let T (n : ℕ) (ω : Ω) := regionStop a (L n ω).ε (L n ω).hε (z ω)
    (L n ω).N (ρ ω) (δ n ω) (L n ω).B (b ω)
  have hTM (n : ℕ) : Measurable (T n) :=
    regionStop_parameter_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b _ ρ (δ n) _ (hεM n) hzM hbM
      (measurable_subtype_coe.comp (hNM n)) hρM (hδM n) (hBM n)
  have hPM : Measurable (physicalGreen a) := by
    have hx := X.continuous.measurable
    have hy := Y.continuous.measurable
    have hj := J.continuous.measurable
    unfold physicalGreen logGreen Q
    fun_prop
  let F (n : ℕ) (ω : Ω) := physicalGreen a (localState a (L n ω).ε (L n ω).hε (z ω) (T n ω) (b ω))
  have hFM (n : ℕ) : Measurable (F n) := hPM.comp
    ((localState_parameter_joint_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b (hεM n) hzM hbM).comp
      ((hTM n).prodMk measurable_id))
  apply measurable_of_tendsto_metrizable hFM
  apply tendsto_pi_nhds.mpr
  intro ω
  exact localizationApproximation_tendsto a ha ha0 (z ω) (hz ω) (ρ ω) (hρ ω) (hr ω) (b ω)
    (fun n => L n ω)
end ExactSLEGreen

 

open MeasureTheory Set
open scoped ENNReal
namespace ExactSLEKernel
noncomputable def cappedDistance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (x : ι → ℂ) (i : ι) : ℝ :=
  (insert b ((Finset.univ.erase i).image fun j => dist (x i) (x j))).min' (by simp)
noncomputable def kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) : ℝ≥0∞ :=
  ∏ i, (ENNReal.ofReal (cappedDistance b x i)) ^ (-α)

section Basic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma le_cappedDistance_iff (b r : ℝ) (x : ι → ℂ) (i : ι) :
    r ≤ cappedDistance b x i ↔ r ≤ b ∧ ∀ j, j ≠ i → r ≤ dist (x i) (x j) := by
  classical
  unfold cappedDistance
  constructor
  · intro h
    refine ⟨h.trans (Finset.min'_le _ _ (by simp)),?_⟩
    intro j hj
    exact h.trans (Finset.min'_le _ _ (by simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]; exact Or.inr ⟨j,hj,rfl⟩))
  · rintro ⟨hb,h⟩
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact h j (Finset.mem_erase.mp hj).1
lemma cappedDistance_le (b : ℝ) (x : ι → ℂ) (i : ι) : cappedDistance b x i ≤ b :=
  ((le_cappedDistance_iff b _ x i).mp le_rfl).1
lemma cappedDistance_le_dist (b : ℝ) (x : ι → ℂ) (i j : ι) (hji : j ≠ i) :
    cappedDistance b x i ≤ dist (x i) (x j) :=
  ((le_cappedDistance_iff b _ x i).mp le_rfl).2 j hji
lemma cappedDistance_pos {b : ℝ} (hb : 0 < b) (x : ι → ℂ) (hx : Function.Injective x) (i : ι) :
    0 < cappedDistance b x i := by
  classical
  have h := Finset.min'_mem (insert b ((Finset.univ.erase i).image fun j => dist (x i) (x j))) (by simp)
  change cappedDistance b x i ∈ _ at h
  rcases Finset.mem_insert.mp h with h|h
  · rwa [h]
  · obtain ⟨j,hj,h⟩ := Finset.mem_image.mp h
    rw [←h]
    exact dist_pos.mpr (fun he => (Finset.mem_erase.mp hj).1 (hx he).symm)
lemma cappedDistance_nonneg {b : ℝ} (hb : 0 ≤ b) (x : ι → ℂ) (i : ι) :
    0 ≤ cappedDistance b x i := (le_cappedDistance_iff _ _ _ _).mpr ⟨hb,fun _ _ => dist_nonneg⟩
end Basic
lemma cappedDistance_cons_succ {m : ℕ} (b : ℝ) (z : ℂ) (x : Fin m → ℂ) (i : Fin m) :
    cappedDistance b (Fin.cons z x) i.succ = min (cappedDistance b x i) (dist z (x i)) := by
  apply le_antisymm
  · apply le_min
    · apply (le_cappedDistance_iff _ _ _ _).mpr
      refine ⟨cappedDistance_le _ _ _,fun j hj => ?_⟩
      simpa using cappedDistance_le_dist b (Fin.cons z x) i.succ j.succ (by simpa using hj)
    · simpa [dist_comm] using cappedDistance_le_dist b (Fin.cons z x) i.succ 0 (Ne.symm (Fin.succ_ne_zero i))
  · apply (le_cappedDistance_iff _ _ _ _).mpr
    refine ⟨(min_le_left _ _).trans (cappedDistance_le _ _ _),?_⟩
    intro j hj
    revert hj
    refine Fin.cases (fun hj => ?_) (fun k hj => ?_) j
    · simp [dist_comm]
    · have hki : k ≠ i := by intro he; subst k; exact hj rfl
      exact (min_le_left _ _).trans (by simpa using cappedDistance_le_dist b x i k hki)
lemma half_cap_unique {m : ℕ} (b : ℝ) (z : ℂ) (x : Fin m → ℂ)
    (i j : Fin m) (hi : dist z (x i) < cappedDistance b x i / 2)
    (hj : dist z (x j) < cappedDistance b x j / 2) : i = j := by
  by_contra hij
  have h1 := cappedDistance_le_dist b x i j (Ne.symm hij)
  have h2 := cappedDistance_le_dist b x j i hij
  have h3 := dist_triangle (x i) z (x j)
  rw [dist_comm (x i) z] at h3
  rw [dist_comm (x j) (x i)] at h2
  linarith
lemma near_cap_nearest {m : ℕ} (b : ℝ) (z : ℂ) (x : Fin m → ℂ)
    (i : Fin m) (hi : dist z (x i) < cappedDistance b x i / 2) :
    cappedDistance b (Fin.cons z x) 0 = dist z (x i) := by
  apply le_antisymm
  · simpa using cappedDistance_le_dist b (Fin.cons z x) 0 i.succ (by simp)
  · apply (le_cappedDistance_iff _ _ _ _).mpr
    refine ⟨by have := cappedDistance_le b x i; have := dist_nonneg (x:=z) (y:=x i); linarith,?_⟩
    intro j hj
    revert hj
    refine Fin.cases (fun hj => False.elim (hj rfl)) (fun k hj => ?_) j
    simp only [Fin.cons_zero,Fin.cons_succ]
    by_cases hki : k=i
    · simp [hki]
    · have h1 := cappedDistance_le_dist b x i k hki
      have h2 := dist_triangle (x i) z (x k)
      rw [dist_comm (x i) z] at h2
      linarith
noncomputable def ipow (α r : ℝ) : ℝ≥0∞ := ENNReal.ofReal r ^ (-α)
lemma ipow_anti {α r s : ℝ} (ha : 0 ≤ α) (hrs : r ≤ s) : ipow α s ≤ ipow α r := by
  unfold ipow
  rw [ENNReal.rpow_neg,ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrs) ha)
lemma ipow_pos {α r : ℝ} (ha : 0 ≤ α) : 0 < ipow α r := by
  rw [ipow,ENNReal.rpow_neg,ENNReal.inv_pos]
  exact ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top
lemma ipow_finite {α r : ℝ} (hr : 0 < r) : ipow α r < ∞ := by
  exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top)
lemma ipow_mul (α : ℝ) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ipow α (r*s) = ipow α r * ipow α s := by
  rw [ipow,ENNReal.ofReal_mul hr,ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  rfl
lemma ipow_twice (α r : ℝ) : ipow (2*α) r = ipow α r * ipow α r := by
  unfold ipow
  rw [show -(2*α)=(-α)*(2:ℕ) by norm_num; ring,ENNReal.rpow_mul,ENNReal.rpow_natCast,pow_two]
lemma cap_factor_sup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℝ} (ha : 0 ≤ α) (b : ℝ) (x : ι → ℂ) (i : ι) :
    ipow α (cappedDistance b x i) = ipow α b ⊔ ⨆ j, if j=i then 0 else ipow α (dist (x i) (x j)) := by
  classical
  apply le_antisymm
  · have h := Finset.min'_mem (insert b ((Finset.univ.erase i).image fun j => dist (x i) (x j))) (by simp)
    change cappedDistance b x i ∈ _ at h
    rcases Finset.mem_insert.mp h with h|h
    · rw [h]; exact le_sup_left
    · obtain ⟨j,hj,hj'⟩ := Finset.mem_image.mp h
      rw [←hj']
      exact (le_iSup_of_le j (by simp [(Finset.mem_erase.mp hj).1])).trans le_sup_right
  · apply sup_le
    · exact ipow_anti ha (cappedDistance_le _ _ _)
    · apply iSup_le
      intro j
      split_ifs with h
      · exact bot_le
      · exact ipow_anti ha (cappedDistance_le_dist _ _ _ _ h)
lemma measurable_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℝ} (ha : 0 ≤ α) (b : ℝ) : Measurable (kernel (ι:=ι) α b) := by
  classical
  unfold kernel
  apply Finset.measurable_prod
  intro i hi
  change Measurable (fun x : ι → ℂ => ipow α (cappedDistance b x i))
  simp_rw [cap_factor_sup ha]
  apply Measurable.sup measurable_const
  apply Measurable.iSup
  intro j
  split_ifs
  · exact measurable_const
  · unfold ipow
    fun_prop
lemma cap_cons_factor_sum {m : ℕ} {α : ℝ} (ha : 0 ≤ α) (b : ℝ)
    (z : ℂ) (x : Fin m → ℂ) :
    ipow α (cappedDistance b (Fin.cons z x) 0) ≤ ipow α b + ∑ i, ipow α (dist z (x i)) := by
  rw [cap_factor_sup ha]
  apply sup_le
  · exact le_self_add
  · apply iSup_le; intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.succ_ne_zero,ite_false,Fin.cons_zero,Fin.cons_succ]
      exact (Finset.single_le_sum (fun k _ => (by positivity : (0:ℝ≥0∞) ≤ ipow α (dist z (x k)))) (Finset.mem_univ j)).trans le_add_self
lemma far_cap_factor {m : ℕ} {α b : ℝ} (ha : 0 ≤ α) (hb : 0 ≤ b)
    (z : ℂ) (x : Fin m → ℂ) (i : Fin m)
    (hi : cappedDistance b x i / 2 ≤ dist z (x i)) :
    ipow α (cappedDistance b (Fin.cons z x) i.succ) ≤ ipow α (1/2) * ipow α (cappedDistance b x i) := by
  have hn := cappedDistance_nonneg hb x i
  have h : cappedDistance b x i / 2 ≤ cappedDistance b (Fin.cons z x) i.succ := by
    rw [cappedDistance_cons_succ]
    exact le_min (by linarith) hi
  have hh := ipow_anti ha h
  convert hh using 1
  rw [show cappedDistance b x i / 2 = cappedDistance b x i * (1/2) by ring, ipow_mul α hn,mul_comm]
lemma cap_compensated {m : ℕ} {α b : ℝ} (ha : 0 ≤ α) (hb : 0 < b)
    (x : Fin m → ℂ) (i : Fin m) :
    1 ≤ ipow α (cappedDistance b x i) * ENNReal.ofReal b ^ α := by
  have h := mul_le_mul' (ipow_anti ha (cappedDistance_le b x i)) (le_refl (ENNReal.ofReal b ^ α))
  have he : ipow α b * ENNReal.ofReal b ^ α = 1 := by
    rw [ipow,←ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) ENNReal.ofReal_ne_top]
    simp
  rwa [he] at h
end ExactSLEKernel
end

end OAI
