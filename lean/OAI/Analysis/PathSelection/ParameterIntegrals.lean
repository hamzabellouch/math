import Mathlib

namespace OAI

/-! Analytic parameter integrals over compact sets and circles. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Metric MeasureTheory Complex
open scoped Real NNReal ENNReal

namespace PathSelection.ParameterPreparation

lemma differentiableAt_integral_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {K : Set ℝ} {F : E → ℝ → ℂ} {D : E → ℝ → E →L[ℂ] ℂ}
    (hU : IsOpen U) (hK : IsCompact K)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ K))
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ K))
    (hd : ∀ a∈U, ∀ t∈K, HasFDerivAt (fun x => F x t) (D a t) a)
    {a : E} (ha : a∈U) :
    DifferentiableAt ℂ (fun x => ∫ t in K, F x t) a := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let A := closedBall a (r/2)
  have hAU : A⊆U := (closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  have hAc : IsCompact A := isCompact_closedBall _ _
  obtain ⟨C,hC⟩ := (hAc.prod hK).exists_bound_of_continuousOn
    (hD.mono (prod_mono hAU Subset.rfl))
  have hFc (x : E) (hx : x∈U) : ContinuousOn (F x) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx,ht⟩)
  have hDc : ContinuousOn (D a) K :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨ha,ht⟩)
  apply HasFDerivAt.differentiableAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict K) (s := A) (bound := fun _ => C)
    (closedBall_mem_nhds a (by linarith))
  · filter_upwards [hU.mem_nhds ha] with x hx
    exact ((hFc x hx).integrableOn_compact hK).aestronglyMeasurable
  · exact (hFc a ha).integrableOn_compact hK
  · exact (hDc.integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro x hx
    exact hC (x,t) ⟨hx,ht⟩
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro x hx
    exact hd x (hAU hx) t ht

 

theorem differentiableOn_circleIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {F : E × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r)
    (hf : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r)) :
    DifferentiableOn ℂ (fun a => ∮ z in C(0,r), F (a,z)) U := by
  let K : Set ℝ := Icc 0 (2*π)
  let c : ℝ → ℂ := circleMap 0 r
  let G : E → ℝ → ℂ := fun a t => deriv c t * F (a,c t)
  let D : E → ℝ → E →L[ℂ] ℂ := fun a t =>
    deriv c t • (fderiv ℂ F (a,c t)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hc : Continuous c := continuous_circleMap 0 r
  have hdc : Continuous (deriv c) := by
    have he : deriv c = fun t => circleMap 0 r t * I := funext (deriv_circleMap 0 r)
    rw [he]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hcmem (t : ℝ) : c t∈sphere (0:ℂ) r := circleMap_mem_sphere 0 hr t
  have hcomp : Continuous (fun p : E × ℝ => (p.1,c p.2)) :=
    continuous_fst.prodMk (hc.comp continuous_snd)
  have hmaps : MapsTo (fun p : E × ℝ => (p.1,c p.2)) (U ×ˢ K) (U ×ˢ sphere 0 r) :=
    fun p hp => ⟨hp.1,hcmem p.2⟩
  have hG : ContinuousOn (Function.uncurry G) (U ×ˢ K) :=
    ((hdc.comp continuous_snd).continuousOn).mul
      (hf.continuousOn.comp hcomp.continuousOn hmaps)
  have hD : ContinuousOn (Function.uncurry D) (U ×ˢ K) := by
    apply ((hdc.comp continuous_snd).continuousOn).smul
    exact (hf.fderiv.continuousOn.comp hcomp.continuousOn hmaps).clm_comp continuousOn_const
  have hd : ∀ a∈U, ∀ t∈K, HasFDerivAt (fun x => G x t) (D a t) a := by
    intro a ha t ht
    have hin : HasFDerivAt (fun x : E => (x,c t)) (ContinuousLinearMap.inl ℂ E ℂ) a :=
      hasFDerivAt_prodMk_left a (c t)
    have h := (hf (a,c t) ⟨ha,hcmem t⟩).differentiableAt.hasFDerivAt.comp a hin
    exact h.const_mul (deriv c t)
  have hdiff : DifferentiableOn ℂ (fun a => ∮ z in C(0,r), F (a,z)) U := by
    intro a ha
    have hdif := differentiableAt_integral_compact hU isCompact_Icc hG hD hd ha
    simp only [circleIntegral_def_Icc,smul_eq_mul]
    exact hdif.differentiableWithinAt
  exact hdiff

 

theorem analyticOnNhd_circleIntegral_one_parameter
    {U : Set ℂ} {F : ℂ × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r)
    (hf : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r)) :
    AnalyticOnNhd ℂ (fun a => ∮ z in C(0,r), F (a,z)) U :=
  (differentiableOn_circleIntegral hU hr hf).analyticOnNhd hU

 

theorem hasFPowerSeriesOnBall_integral
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : α → E → ℂ} {p : α → FormalMultilinearSeries ℂ E ℂ}
    {a : E} {R : ℝ≥0} (hR : 0<R)
    (hp : ∀ᵐ t ∂μ, HasFPowerSeriesOnBall (F t) (p t) a R)
    (hi : ∀ n, Integrable (fun t => p t n) μ)
    (hs : Summable (fun n => (∫ t, ‖p t n‖ ∂μ) * (R:ℝ)^n)) :
    HasFPowerSeriesOnBall (fun x => ∫ t, F t x ∂μ)
      (fun n => ∫ t, p t n ∂μ) a R := by
  let q : FormalMultilinearSeries ℂ E ℂ := fun n => ∫ t, p t n ∂μ
  have hb (n : ℕ) : ‖q n‖ * (R:ℝ)^n ≤ (∫ t, ‖p t n‖ ∂μ) * (R:ℝ)^n :=
    mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
  refine ⟨?_,by exact_mod_cast hR,?_⟩
  · apply q.le_radius_of_bound (∑' n, (∫ t, ‖p t n‖ ∂μ) * (R:ℝ)^n)
    intro n
    exact (hb n).trans (hs.le_tsum n (fun _ _ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (by positivity)))
  · intro x hx
    have hxR : ‖x‖≤(R:ℝ) := by
      have hh : (‖x‖₊:ℝ≥0∞)<R := mem_eball_zero_iff.mp hx
      exact_mod_cast hh.le
    have hpi (n : ℕ) : Integrable (fun t => p t n (fun _ => x)) μ :=
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) ℂ (fun _ => x)).integrable_comp (hi n)
    have hpn (n : ℕ) : (∫ t, ‖p t n (fun _ => x)‖ ∂μ) ≤
        (∫ t, ‖p t n‖ ∂μ) * (R:ℝ)^n := by
      rw [← integral_mul_const]
      apply integral_mono (hpi n).norm ((hi n).norm.mul_const _)
      intro t
      apply ((p t n).le_opNorm (fun _ => x)).trans
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hxR n) (norm_nonneg _)
    have hsum : Summable (fun n => ∫ t, ‖p t n (fun _ => x)‖ ∂μ) :=
      Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hpn hs
    have hh := hasSum_integral_of_summable_integral_norm hpi hsum
    have he : (∫ t, (∑' n, p t n (fun _ => x)) ∂μ) = ∫ t, F t (a+x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp] with t ht
      exact (ht.hasSum hx).tsum_eq
    rw [he] at hh
    simpa only [ContinuousMultilinearMap.integral_apply (hi _)] using hh

 

lemma changeOrigin_uniform_majorant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : FormalMultilinearSeries ℂ E ℂ)
    {r R : ℝ≥0} (hr : (r+R:ℝ≥0∞)<p.radius) :
    ∃ M : ℕ → ℝ≥0, Summable (fun n => (M n:ℝ)*(R:ℝ)^n) ∧
      ∀ x, ‖x‖₊≤r → ∀ n, ‖p.changeOrigin x n‖₊≤M n := by
  let M : ℕ → ℝ≥0 := fun k =>
    ∑' s : Σ l : ℕ, {s : Finset (Fin (k+l)) // s.card=l}, ‖p (k+s.1)‖₊*r^s.1
  have hrp : (r:ℝ≥0∞)<p.radius := (le_add_of_nonneg_right (by positivity)).trans_lt hr
  have hsum : Summable (fun n => M n * R^n) := by
    simpa only [M, NNReal.tsum_mul_right] using
      (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2
  refine ⟨M,by exact_mod_cast NNReal.summable_coe.mpr hsum,?_⟩
  intro x hx n
  have hxp : (‖x‖₊:ℝ≥0∞)<p.radius :=
    (by exact_mod_cast hx : (‖x‖₊:ℝ≥0∞)≤r).trans_lt hrp
  apply (p.nnnorm_changeOrigin_le n hxp).trans
  exact Summable.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx s.1) (by positivity))
    (p.changeOriginSeries_summable_aux₂ hxp n) (p.changeOriginSeries_summable_aux₂ hrp n)

 

theorem analyticAt_integral_shift_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set ℝ} (hK : MeasurableSet K)
    [IsFiniteMeasure (volume.restrict K)]
    {F : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ} {a : E} {ρ : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall F p a ρ)
    {v : ℝ → E} {w : ℝ → ℂ}
    (hv : ContinuousOn v K) (hw : ContinuousOn w K)
    {r R : ℝ≥0} (hR : 0<R) (hr : (r+R:ℝ≥0∞)<ρ)
    (hb : ∀ t∈K, ‖v t‖₊≤r)
    {C : ℝ} (hC : 0≤C) (hwb : ∀ t∈K, ‖w t‖≤C) :
    AnalyticAt ℂ (fun x => ∫ t in K, w t * F (x+v t)) a := by
  let μ := volume.restrict K
  let q : ℝ → FormalMultilinearSeries ℂ E ℂ := fun t => w t • p.changeOrigin (v t)
  have hrp : (r+R:ℝ≥0∞)<p.radius := hr.trans_le hp.r_le
  obtain ⟨M,hM,hbound⟩ := changeOrigin_uniform_majorant p hrp
  have hrr : (r:ℝ≥0∞)<ρ := (le_add_of_nonneg_right (by positivity)).trans_lt hr
  have hvr (t : ℝ) (ht : t∈K) : (‖v t‖₊:ℝ≥0∞)<ρ :=
    (by exact_mod_cast hb t ht : (‖v t‖₊:ℝ≥0∞)≤r).trans_lt hrr
  have hq (n : ℕ) : ContinuousOn (fun t => q t n) K := by
    apply hw.smul
    exact (p.hasFPowerSeriesOnBall_changeOrigin n (hp.r_pos.trans_le hp.r_le)).continuousOn.comp hv
      (fun t ht => mem_eball_zero_iff.mpr ((hvr t ht).trans_le hp.r_le))
  have hqn (n : ℕ) : ∀ t∈K, ‖q t n‖≤C*(M n:ℝ) := by
    intro t ht
    change ‖w t • p.changeOrigin (v t) n‖≤_
    rw [norm_smul]
    exact mul_le_mul (hwb t ht) (by exact_mod_cast hbound (v t) (hb t ht) n)
      (norm_nonneg _) hC
  have hi (n : ℕ) : Integrable (fun t => q t n) μ :=
    Integrable.of_bound ((hq n).aestronglyMeasurable hK) (C*(M n:ℝ))
      (by filter_upwards [ae_restrict_mem hK] with t ht; exact hqn n t ht)
  have hs : Summable (fun n => (∫ t, ‖q t n‖ ∂μ)*(R:ℝ)^n) := by
    have hmajor := hM.mul_left (μ.real univ * C)
    apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (by positivity)) _ hmajor
    intro n
    have hn : (∫ t, ‖q t n‖ ∂μ) ≤ μ.real univ * (C*(M n:ℝ)) := by
      calc
        _ ≤ ∫ _t, C*(M n:ℝ) ∂μ := integral_mono_ae (hi n).norm (integrable_const _)
          (by filter_upwards [ae_restrict_mem hK] with t ht; exact hqn n t ht)
        _ = _ := by simp [integral_const]
    calc
      _ ≤ μ.real univ * (C*(M n:ℝ)) * (R:ℝ)^n :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by ring
  have hpq : ∀ᵐ t ∂μ, HasFPowerSeriesOnBall (fun x => w t * F (x+v t)) (q t) a R := by
    filter_upwards [ae_restrict_mem hK] with t ht
    have hrad : (R:ℝ≥0∞) ≤ ρ - (‖v t‖₊:ℝ≥0∞) := by
      apply ENNReal.le_sub_of_add_le_right (by finiteness)
      calc
        (R:ℝ≥0∞) + (‖v t‖₊:ℝ≥0∞) ≤ R+r := add_le_add_right (by exact_mod_cast hb t ht : (‖v t‖₊:ℝ≥0∞)≤r) _
        _ ≤ ρ := by simpa [add_comm] using hr.le
    have h := ((hp.changeOrigin (hvr t ht)).comp_sub (-(v t))).mono
      (by exact_mod_cast hR) hrad
    simpa [q,sub_neg_eq_add,Pi.smul_def,smul_eq_mul] using h.const_smul (c := w t)
  exact (hasFPowerSeriesOnBall_integral hR hpq hi hs).analyticAt

 
lemma analyticAt_integral_finite_cover
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : E} {F : E → ℝ → ℂ} {K : Set ℝ} {B : ι → Set ℝ}
    (T : Finset ι) (hB : ∀ i, MeasurableSet (B i))
    (hi : ∀ᶠ x in 𝓝 a, IntegrableOn (F x) K)
    (hl : ∀ i∈T, ∀ S, MeasurableSet S → S⊆K → S⊆B i →
      AnalyticAt ℂ (fun x => ∫ t in S, F x t) a) :
    ∀ S, MeasurableSet S → S⊆K → S⊆⋃ i∈T, B i →
      AnalyticAt ℂ (fun x => ∫ t in S, F x t) a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      intro S hS hSK hc
      have he : S=∅ := by simpa using hc
      simpa only [he,setIntegral_empty] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (0:ℂ)) a)
  | @insert i T hiT ih =>
      intro S hS hSK hc
      have h1 := hl i (Finset.mem_insert_self i T) (S∩B i) (hS.inter (hB i))
        (inter_subset_left.trans hSK) inter_subset_right
      have h2 : AnalyticAt ℂ (fun x => ∫ t in S\B i, F x t) a := by
        apply ih (fun j hj => hl j (Finset.mem_insert_of_mem hj)) (S\B i)
          (hS.diff (hB i)) (sdiff_subset.trans hSK)
        intro t ht
        have hh := hc ht.1
        simp only [mem_iUnion,Finset.mem_insert,exists_prop] at hh ⊢
        obtain ⟨j,hj,htj⟩ := hh
        rcases hj with rfl|hj
        · exact False.elim (ht.2 htj)
        · exact ⟨j,hj,htj⟩
      apply (h1.add h2).congr
      filter_upwards [hi] with x hx
      have he := setIntegral_union
        (show Disjoint (S∩B i) (S\B i) from disjoint_left.mpr (fun t ht hu => hu.2 ht.2))
        (hS.diff (hB i)) (hx.mono_set (inter_subset_left.trans hSK))
        (hx.mono_set (sdiff_subset.trans hSK))
      simpa only [inter_union_sdiff,Pi.add_apply] using he.symm

 

theorem analyticOnNhd_integral_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {K : Set ℝ} {c w : ℝ → ℂ} {F : E × ℂ → ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hc : Continuous c) (hw : Continuous w)
    (hf : AnalyticOnNhd ℂ F (U ×ˢ (c '' K))) :
    AnalyticOnNhd ℂ (fun a => ∫ t in K, w t * F (a,c t)) U := by
  classical
  intro a ha
  obtain ⟨C₀,hC₀⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
  let C := max C₀ 0
  have hC : 0≤C := le_max_right _ _
  have hwb : ∀ t∈K, ‖w t‖≤C := fun t ht => (hC₀ t ht).trans (le_max_left _ _)
  have hchart : ∀ t : K, ∃ δ : ℝ, 0<δ ∧ ∀ S : Set ℝ,
      MeasurableSet S → S⊆K → S⊆c ⁻¹' ball (c t) δ →
      AnalyticAt ℂ (fun x => ∫ s in S, w s * F (x,c s)) a := by
    intro t
    obtain ⟨p,ρ,hp⟩ := hf (a,c t) ⟨ha,mem_image_of_mem c t.property⟩
    obtain ⟨b,hb0,hbρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
    have hb : (0:ℝ≥0)<b := by exact_mod_cast hb0
    let δ : ℝ≥0 := b/3
    have hδ : 0<δ := div_pos hb (by norm_num)
    have hrad : (δ+δ:ℝ≥0∞)<ρ := by
      apply lt_trans _ hbρ
      exact_mod_cast (show δ+δ<b from by dsimp [δ]; linarith)
    refine ⟨δ,by exact_mod_cast hδ,?_⟩
    intro S hS hSK hSB
    let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
      ((measure_mono hSK).trans_lt hK.measure_lt_top).ne
    let v : ℝ → E × ℂ := fun s => (0,c s-c t)
    have hv : ContinuousOn v S :=
      (continuous_const.prodMk (hc.sub continuous_const)).continuousOn
    have hvb : ∀ s∈S, ‖v s‖₊≤δ := by
      intro s hs
      have hh := hSB hs
      have hn : ‖c s-c t‖≤(δ:ℝ) := (mem_ball_iff_norm.mp hh).le
      change ‖((0,c s-c t) : E × ℂ)‖₊≤δ
      rw [Prod.nnnorm_mk,nnnorm_zero,max_eq_right (by positivity)]
      exact_mod_cast hn
    have hh := analyticAt_integral_shift_piece hS hp hv hw.continuousOn hδ hrad hvb hC
      (fun s hs => hwb s (hSK hs))
    have hi : AnalyticAt ℂ (fun x : E => (x,c t)) a := analyticAt_id.prod analyticAt_const
    have hh' := hh.comp (f := fun x : E => (x,c t)) hi
    apply hh'.congr
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with s
    congr 1
    apply congrArg F
    change (x,c t)+(0,c s-c t)=(x,c s)
    ext <;> simp
  choose δ hδ hlocal using hchart
  let B : K → Set ℝ := fun t => c ⁻¹' ball (c t) (δ t)
  have hBo (t : K) : IsOpen (B t) := isOpen_ball.preimage hc
  have hcover : K⊆⋃ t : K, B t := by
    intro s hs
    exact mem_iUnion.mpr ⟨⟨s,hs⟩,by simp [B,hδ]⟩
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover B hBo hcover
  have hi : ∀ᶠ x in 𝓝 a, IntegrableOn (fun t => w t * F (x,c t)) K := by
    filter_upwards [hU.mem_nhds ha] with x hx
    apply ContinuousOn.integrableOn_compact hK
    apply hw.continuousOn.mul
    exact hf.continuousOn.comp (continuous_const.prodMk hc).continuousOn
      (fun t ht => ⟨hx,mem_image_of_mem c ht⟩)
  exact analyticAt_integral_finite_cover T (fun t => (hBo t).measurableSet) hi
    (fun t _ => hlocal t) K hK.measurableSet Subset.rfl hT

 

theorem analyticOnNhd_circleIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {F : E × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r)
    (hf : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r)) :
    AnalyticOnNhd ℂ (fun a => ∮ z in C(0,r), F (a,z)) U := by
  have hdc : Continuous (deriv (circleMap 0 r)) := by
    have he : deriv (circleMap 0 r) = fun t => circleMap 0 r t * I :=
      funext (deriv_circleMap 0 r)
    rw [he]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hh := analyticOnNhd_integral_compact (K := Icc 0 (2*π)) hU isCompact_Icc (continuous_circleMap 0 r) hdc
    (hf.mono (prod_mono Subset.rfl (by rintro _ ⟨t,ht,rfl⟩; exact circleMap_mem_sphere 0 hr t)))
  simpa only [circleIntegral_def_Icc,smul_eq_mul] using hh

end PathSelection.ParameterPreparation
end

end OAI
