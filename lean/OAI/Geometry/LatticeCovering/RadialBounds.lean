import OAI.Geometry.LatticeCovering.LogConcavity

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Isotropization
open scoped Topology

lemma radial_integral_set {k : ℕ} [Nontrivial (E k)] (φ : ℝ → ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x : E k in norm ⁻¹' A, φ ‖x‖)=
      ((k:ℝ)*volume.real (Metric.ball (0:E k) 1))*(∫ r in Ioi 0 ∩ A, r^(k-1)*φ r) := by
  rw [←integral_indicator (hA.preimage measurable_norm)]
  have he : (norm ⁻¹' A).indicator (fun x : E k => φ ‖x‖)=fun x => (A.indicator φ) ‖x‖ := by
    ext x
    by_cases hx : ‖x‖ ∈ A <;> simp [hx]
  rw [he,integral_fun_norm_addHaar (volume : Measure (E k))]
  simp only [finrank_euclideanSpace_fin,nsmul_eq_mul,smul_eq_mul]
  rw [mul_assoc]
  congr 1
  have he' : (fun r : ℝ => r^(k-1)*A.indicator φ r)=A.indicator (fun r => r^(k-1)*φ r) := by
    ext r
    by_cases hr : r ∈ A <;> simp [hr]
  rw [he',integral_indicator hA,Measure.restrict_restrict hA,inter_comm]

lemma weighted_profile_tendsto_zero {φ : ℝ → ℝ} {m : ℕ}
    (hn : ∀ r, 0 ≤ φ r)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    Tendsto (fun r : ℝ => r^m*φ r) atTop (𝓝 0) := by
  have hupper : ∀ r : ℝ, 0 < r → r^m*φ r ≤
      (((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))/r := by
    intro r hr
    have H := radial_integral_lower (m := m) hr hn
      (fun t ht => hmono t r ht.1 ht.2) hi
    apply (le_div_iff₀ hr).mpr
    have HH := (div_le_iff₀ (show 0 < (m:ℝ)+1 by positivity)).mp H
    linarith
  have ht : Tendsto (fun r : ℝ => (((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))/r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := ((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))).mul tendsto_inv_atTop_zero
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact mul_nonneg (pow_nonneg hr.le _) (hn r)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hupper r hr



theorem ScalarLogConcave.exists_shell_radius {k : ℕ} (hk : 2 ≤ k)
    {φ : ℝ → ℝ} (hφ : ScalarLogConcave φ) (hc : Continuous φ) (hp : 0 < φ 1)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r)
    (hi : Integrable (fun x : E k => φ ‖x‖) volume) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, φ ‖x‖)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, φ ‖x‖) ≤
        (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))*
          (∫ x : E k, φ ‖x‖) := by
  have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa only [finrank_euclideanSpace_fin] using (show 0 < k by omega))
  have hw : IntegrableOn (fun r : ℝ => r^(k-1)*φ r) (Ioi 0) volume := by
    simpa only [finrank_euclideanSpace_fin,smul_eq_mul] using
      (integrable_fun_norm_addHaar (volume : Measure (E k))).mp hi
  obtain ⟨r₀,hr₀,hφ₀,hmax⟩ := exists_weighted_mode (m := k-1) (by omega) hc hp
    (weighted_profile_tendsto_zero hφ.1 hmono hw)
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have H := hφ.shell_integral_bound (m := k-1) (by omega) hr₀ hε hε1 hφ₀ hmax
    (fun r hr => hmono r r₀ hr.1 hr.2) hw
  have heL : Ioi 0 ∩ Iic ((1-ε)*r₀)=Ioc 0 ((1-ε)*r₀) := by ext r; simp
  have heU : Ioi 0 ∩ Ioi ((1+ε)*r₀)=Ioi ((1+ε)*r₀) := inter_eq_right.mpr (by
    intro r hr
    exact (show (0:ℝ) < (1+ε)*r₀ by positivity).trans hr)
  rw [show {x : E k | ‖x‖ ≤ (1-ε)*r₀} = norm ⁻¹' Iic ((1-ε)*r₀) from rfl,
    show {x : E k | (1+ε)*r₀ < ‖x‖} = norm ⁻¹' Ioi ((1+ε)*r₀) from rfl,
    radial_integral_set φ measurableSet_Iic,radial_integral_set φ measurableSet_Ioi,
    heL,heU,integral_fun_norm_addHaar (volume : Measure (E k)) φ]
  simp only [finrank_euclideanSpace_fin,nsmul_eq_mul,smul_eq_mul]
  have HV := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)*volume.real (Metric.ball (0:E k) 1) by positivity)
  ring_nf at HV ⊢
  exact HV


end SingleLatticeCovering.Prekopa
namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization
open scoped RealInnerProductSpace Topology

noncomputable def radialInf {k : ℕ} (f : E k → ℝ) (y : E k) : ℝ :=
  ⨅ U : E k ≃ₗᵢ[ℝ] E k, f (U y)

lemma radialInf_bddBelow {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    BddBelow (Set.range (fun U : E k ≃ₗᵢ[ℝ] E k => f (U y))) :=
  ⟨0,by rintro _ ⟨U,rfl⟩; exact hf _⟩

lemma radialInf_nonneg {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    0 ≤ radialInf f y := by
  unfold radialInf
  exact le_ciInf (fun U => hf (U y))

lemma radialInf_le {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k)
    (U : E k ≃ₗᵢ[ℝ] E k) : radialInf f y ≤ f (U y) :=
  ciInf_le (radialInf_bddBelow hf y) U

lemma radialInf_le_self {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    radialInf f y ≤ f y := radialInf_le hf y (LinearIsometryEquiv.refl ℝ (E k))

lemma radialInf_invariant {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    (U : E k ≃ₗᵢ[ℝ] E k) (y : E k) : radialInf f (U y)=radialInf f y := by
  apply le_antisymm
  · apply le_ciInf
    intro V
    have H := radialInf_le hf (U y) (U.symm.trans V)
    simpa only [LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply] using H
  · apply le_ciInf
    intro V
    exact radialInf_le hf y (U.trans V)

lemma radialInf_norm_eq {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {y z : E k} (h : ‖y‖=‖z‖) : radialInf f y=radialInf f z := by
  have H := radialInf_invariant hf (Submodule.reflection (ℝ ∙ (y-z))ᗮ) y
  rw [Submodule.reflection_sub h] at H
  exact H.symm

lemma radialInf_upperSemicontinuous {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    (hc : Continuous f) : UpperSemicontinuous (radialInf f) := by
  exact upperSemicontinuous_ciInf (radialInf_bddBelow hf)
    (fun U => (hc.comp U.continuous).upperSemicontinuous)

lemma radialInf_logConcave {k : ℕ} {f : E k → ℝ} (hf : LogConcave f) :
    LogConcave (radialInf f) := by
  refine ⟨radialInf_nonneg hf.1,fun y z a b ha hb hab => ?_⟩
  apply le_ciInf
  intro U
  calc
    _ ≤ (f (U y))^a*(f (U z))^b := mul_le_mul
      (Real.rpow_le_rpow (radialInf_nonneg hf.1 y) (radialInf_le hf.1 y U) ha.le)
      (Real.rpow_le_rpow (radialInf_nonneg hf.1 z) (radialInf_le hf.1 z U) hb.le)
      (Real.rpow_nonneg (radialInf_nonneg hf.1 z) b) (Real.rpow_nonneg (hf.1 _) a)
    _ ≤ f (a•U y+b•U z) := hf.2 _ _ _ _ ha hb hab
    _ = _ := by rw [map_add,map_smul,map_smul]

lemma radialInf_approximation {k : ℕ} {f M : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {ε : ℝ} (hrad : ∀ y z, ‖y‖=‖z‖ → M y=M z)
    (herr : ∀ y, |f y-M y| ≤ ε) (y : E k) : |radialInf f y-M y| ≤ ε := by
  apply abs_le.mpr
  constructor
  · have H : M y-ε ≤ radialInf f y := by
      apply le_ciInf
      intro U
      have HH := (abs_le.mp (herr (U y))).1
      rw [hrad (U y) y (U.norm_map y)] at HH
      linarith
    linarith
  · exact (sub_le_sub_right (radialInf_le_self hf y) (M y)).trans (abs_le.mp (herr y)).2

lemma logConcave_min {k : ℕ} {f : E k → ℝ} (hf : LogConcave f)
    (y z : E k) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    min (f y) (f z) ≤ f (a•y+b•z) := by
  have hn : 0 ≤ min (f y) (f z) := le_min (hf.1 _) (hf.1 _)
  calc
    _ = (min (f y) (f z))^a*(min (f y) (f z))^b := by
      by_cases h0 : min (f y) (f z)=0
      · simp [h0,Real.zero_rpow (ne_of_gt ha)]
      rw [←Real.rpow_add (lt_of_le_of_ne hn (Ne.symm h0)),hab,Real.rpow_one]
    _ ≤ (f y)^a*(f z)^b := mul_le_mul
      (Real.rpow_le_rpow hn (min_le_left _ _) ha.le)
      (Real.rpow_le_rpow hn (min_le_right _ _) hb.le)
      (Real.rpow_nonneg hn _) (Real.rpow_nonneg (hf.1 _) _)
    _ ≤ _ := hf.2 _ _ _ _ ha hb hab

lemma radialInf_smul_mono {k : ℕ} {f : E k → ℝ} (hf : LogConcave f)
    (y : E k) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : radialInf f y ≤ radialInf f (a•y) := by
  rcases eq_or_lt_of_le ha1 with rfl | ha1
  · simp
  have hn : radialInf f (-y)=radialInf f y := radialInf_norm_eq hf.1 (norm_neg y)
  have H := logConcave_min (radialInf_logConcave hf) y (-y)
    (a := (1+a)/2) (b := (1-a)/2) (by linarith) (by linarith) (by ring)
  rw [hn,min_self] at H
  convert H using 1
  congr 1
  module




end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization
open scoped RealInnerProductSpace Topology

lemma radialInf_abs_sub_le {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {y z : E k} {ε : ℝ}
    (h : ∀ U : E k ≃ₗᵢ[ℝ] E k, |f (U y)-f (U z)| ≤ ε) :
    |radialInf f y-radialInf f z| ≤ ε := by
  have hyn : radialInf f y-ε ≤ radialInf f z := by
    apply le_ciInf
    intro U
    have H := (abs_le.mp (h U)).2
    linarith [radialInf_le hf y U]
  have hzn : radialInf f z-ε ≤ radialInf f y := by
    apply le_ciInf
    intro U
    have H := (abs_le.mp (h U)).1
    linarith [radialInf_le hf z U]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma continuous_radialInf {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    (hc : Continuous f) : Continuous (radialInf f) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hu := (isCompact_closedBall (0:E k) (‖y‖+1)).uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (ε/2) (by linarith)
  refine ⟨min δ 1,lt_min hδ (by norm_num),fun z hz => ?_⟩
  have hzd : dist z y < δ := hz.trans_le (min_le_left _ _)
  have hz1 : dist z y < 1 := hz.trans_le (min_le_right _ _)
  have hzn : ‖z‖ ≤ ‖y‖+1 := by
    exact norm_le_norm_add_const_of_dist_le hz1.le
  have H : |radialInf f z-radialInf f y| ≤ ε/2 := by
    apply radialInf_abs_sub_le hf
    intro U
    have hzy : U z ∈ Metric.closedBall (0:E k) (‖y‖+1) := by
      simpa only [Metric.mem_closedBall,dist_zero_right,U.norm_map] using hzn
    have hyy : U y ∈ Metric.closedBall (0:E k) (‖y‖+1) := by
      simp only [Metric.mem_closedBall,dist_zero_right,U.norm_map]
      linarith
    have HH := hclose (U z) hzy (U y) hyy (by simpa only [U.dist_map] using hzd)
    exact le_of_lt (by simpa only [Real.dist_eq] using HH)
  rw [Real.dist_eq]
  linarith

lemma radialInf_pos {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 < f y)
    (hc : Continuous f) (y : E k) : 0 < radialInf f y := by
  have hne : (Metric.sphere (0:E k) ‖y‖).Nonempty := ⟨y,by simp⟩
  obtain ⟨z,hz,hmin⟩ := (isCompact_sphere (0:E k) ‖y‖).exists_isMinOn hne hc.continuousOn
  apply (hf z).trans_le
  apply le_ciInf
  intro U
  exact hmin (by simp)



end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization Prekopa
open scoped RealInnerProductSpace Topology

lemma radialInf_integrable {k : ℕ} {f : E k → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hc : Continuous f) (hi : Integrable f volume) : Integrable (radialInf f) volume := by
  apply hi.mono' (continuous_radialInf hf hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (radialInf_nonneg hf x)] using radialInf_le_self hf x)

lemma scalarLogConcave_profile {k : ℕ} {f : E k → ℝ} (hf : LogConcave f) (e : E k) :
    ScalarLogConcave (fun r : ℝ => radialInf f (r•e)) := by
  refine ⟨fun r => radialInf_nonneg hf.1 _,fun r s a b ha hb hab => ?_⟩
  have H := (radialInf_logConcave hf).2 (r•e) (s•e) a b ha hb hab
  simpa only [add_smul,mul_smul] using H


theorem radialInf_shell_radius {k : ℕ} (hk : 2 ≤ k) {f : E k → ℝ}
    (hf : LogConcave f) (hp : ∀ x, 0 < f x) (hc : Continuous f) (hi : Integrable f volume) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, radialInf f x)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, radialInf f x) ≤
        (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))*
          (∫ x : E k, radialInf f x) := by
  have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (show 0 < k by omega))
  obtain ⟨e,he⟩ := exists_norm_eq (E k) (show (0:ℝ) ≤ 1 by norm_num)
  let φ : ℝ → ℝ := fun r => radialInf f (r•e)
  have hre (x : E k) : radialInf f (‖x‖•e)=radialInf f x := by
    apply radialInf_norm_eq hf.1
    simp only [norm_smul,Real.norm_eq_abs,abs_norm,he,mul_one]
  have hcont : Continuous φ := (continuous_radialInf hf.1 hc).comp (by fun_prop)
  have hpos : 0 < φ 1 := radialInf_pos hp hc _
  have hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r := by
    intro r s hr hrs
    have hs : 0 < s := hr.trans_le hrs
    have H := radialInf_smul_mono hf (s•e) (a := r/s) (by positivity)
      ((div_le_one hs).mpr hrs)
    dsimp only [φ]
    convert H using 1
    rw [smul_smul,div_mul_cancel₀ r (ne_of_gt hs)]
  have hint : Integrable (fun x : E k => φ ‖x‖) volume := by
    simp only [φ,hre]
    exact radialInf_integrable hf.1 hc hi
  obtain ⟨r₀,hr₀,H⟩ := (scalarLogConcave_profile hf e).exists_shell_radius hk hcont hpos hmono hint
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  simpa only [hre] using H ε hε hε1


end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization Prekopa
open scoped ENNReal RealInnerProductSpace Topology

lemma setIntegral_transfer_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) {B A : Set Ω}
    (hB : MeasurableSet B) (hA : MeasurableSet A) (hvB : μ B ≠ ∞)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ x ∈ B, g x ≤ f x+δ) :
    (∫ x in A, g x ∂μ) ≤ (∫ x in A, f x ∂μ)+δ*μ.real B+(∫ x in Bᶜ, g x ∂μ) := by
  classical
  have hd : Integrable (B.indicator (fun _ : Ω => δ)) μ :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hvB)
  have hsum : Integrable (fun x => A.indicator f x+B.indicator (fun _ => δ) x) μ := (hf.indicator hA).add hd
  have hpoint (x : Ω) : A.indicator g x ≤
      A.indicator f x+B.indicator (fun _ => δ) x+Bᶜ.indicator g x := by
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
    · simp only [indicator_of_mem ha,indicator_of_mem hb,indicator_of_notMem (show x ∉ Bᶜ from fun h => h hb),add_zero]
      exact hclose x hb
    · simp only [indicator_of_mem ha,indicator_of_notMem hb,indicator_of_mem (show x ∈ Bᶜ from hb),add_zero]
      linarith [hfn x]
    · simp only [indicator_of_notMem ha,indicator_of_mem hb,indicator_of_notMem (show x ∉ Bᶜ from fun h => h hb),zero_add,add_zero]
      exact hδ
    · simp only [indicator_of_notMem ha,indicator_of_notMem hb,indicator_of_mem (show x ∈ Bᶜ from hb),zero_add]
      exact hgn x
  have H := integral_mono (hg.indicator hA) (hsum.add (hg.indicator hB.compl)) hpoint
  change (∫ x, A.indicator g x ∂μ) ≤ ∫ x, A.indicator f x+B.indicator (fun _ => δ) x+Bᶜ.indicator g x ∂μ at H
  rw [integral_add hsum (hg.indicator hB.compl),integral_add (hf.indicator hA) hd,
    integral_indicator hA,integral_indicator hA,integral_indicator hB,integral_indicator hB.compl,
    integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H ⊢
  rw [mul_comm _ δ] at H
  exact H

lemma radialInf_integral_le {k : ℕ} {f : E k → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hc : Continuous f) (hi : Integrable f volume) :
    (∫ x : E k, radialInf f x) ≤ ∫ x : E k, f x :=
  integral_mono (radialInf_integrable hf hc hi) hi (radialInf_le_self hf)




theorem radial_model_shell {k : ℕ} (hk : 2 ≤ k) {f M : E k → ℝ}
    (hf : LogConcave f) (hp : ∀ x, 0 < f x) (hc : Continuous f)
    (hi : Integrable f volume) (hmass : ∫ x, f x=1)
    (hMi : Integrable M volume) (hMn : ∀ x, 0 ≤ M x)
    (hMr : ∀ x y, ‖x‖=‖y‖ → M x=M y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ x, |f x-M x| ≤ δ)
    (T : ℝ) : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, M x)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, M x) ≤
      (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
        2*(δ*volume.real (Metric.closedBall (0:E k) T)+
          (∫ x : E k in (Metric.closedBall (0:E k) T)ᶜ, M x)) := by
  obtain ⟨r₀,hr₀,H⟩ := radialInf_shell_radius hk hf hp hc hi
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have hq : Integrable (radialInf f) volume := radialInf_integrable hf.1 hc hi
  have hq1 : (∫ x : E k, radialInf f x) ≤ 1 := by
    rw [←hmass]; exact radialInf_integral_le hf.1 hc hi
  have happ := radialInf_approximation hf.1 hMr hclose
  have hcl : ∀ x ∈ Metric.closedBall (0:E k) T, M x ≤ radialInf f x+δ := by
    intro x _
    have hh := (abs_le.mp (happ x)).1
    linarith
  have hb : MeasurableSet (Metric.closedBall (0:E k) T) := Metric.isClosed_closedBall.measurableSet
  have hvb : volume (Metric.closedBall (0:E k) T) ≠ ∞ := (isCompact_closedBall _ _).measure_ne_top
  have hlo := setIntegral_transfer_error volume (A := {x : E k | ‖x‖ ≤ (1-ε)*r₀}) hq hMi (radialInf_nonneg hf.1) hMn hb
    (measurableSet_le measurable_norm measurable_const) hvb hδ hcl
  have hhi := setIntegral_transfer_error volume (A := {x : E k | (1+ε)*r₀ < ‖x‖}) hq hMi (radialInf_nonneg hf.1) hMn hb
    (measurableSet_lt measurable_const measurable_norm) hvb hδ hcl
  have hcoeff : 0 ≤ 4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9) := by positivity
  have HH := (H ε hε hε1).trans (mul_le_of_le_one_right hcoeff hq1)
  linarith [hlo,hhi]


end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators RealInnerProductSpace

lemma euclidean_sq_weighted {D : ℕ} (u v : E D) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ‖a•u+b•v‖^2 ≤ a*‖u‖^2+b*‖v‖^2 := by
  rw [norm_add_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg ha,abs_of_nonneg hb,real_inner_smul_left,real_inner_smul_right]
  have H := mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖u-v‖)
  rw [norm_sub_sq_real] at H
  have he : b=1-a := by linarith
  subst b
  nlinarith [H]

noncomputable def smoothingKernel {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) (x : RV n) : ℝ :=
  Real.exp (-c*‖y-A x‖^2)

lemma smoothingKernel_positive {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) (x : RV n) :
    0 < smoothingKernel A c y x := Real.exp_pos _

lemma smoothingKernel_le_one {n D : ℕ} (A : RV n →ₗ[ℝ] E D) {c : ℝ} (hc : 0 ≤ c) (y : E D) (x : RV n) :
    smoothingKernel A c y x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖y-A x‖]

lemma continuous_smoothingKernel {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) :
    Continuous (fun p : E D × RV n => smoothingKernel A c p.1 p.2) := by
  unfold smoothingKernel
  fun_prop

lemma continuous_smoothingKernel_right {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) :
    Continuous (smoothingKernel A c y) := by
  unfold smoothingKernel
  fun_prop

lemma smoothingKernel_weighted {n D : ℕ} (A : RV n →ₗ[ℝ] E D) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (y z : E D) (u v : RV n) :
    (smoothingKernel A c y u)^a*(smoothingKernel A c z v)^b ≤
      smoothingKernel A c (a•y+b•z) (a•u+b•v) := by
  have he : (a•y+b•z)-A (a•u+b•v)=a•(y-A u)+b•(z-A v) := by
    simp only [map_add,map_smul]
    module
  simp only [smoothingKernel,←Real.exp_mul,←Real.exp_add,he]
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left (euclidean_sq_weighted (y-A u) (z-A v) ha hb hab) hc
  nlinarith

lemma soft_smoothing_gaussianBound {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (y : E D) :
    GaussianBound (fun x => softIndicator K t x*smoothingKernel A c y x) := by
  obtain ⟨B,r,hB,hr,hbound⟩ := softIndicator_gaussianBound hK hne ht
  refine ⟨B,r,hB,hr,fun x => ?_⟩
  rw [abs_of_pos (mul_pos (softIndicator_positive K t x) (smoothingKernel_positive A c y x))]
  exact (mul_le_of_le_one_right (softIndicator_positive K t x).le (smoothingKernel_le_one A hc y x)).trans
    (by simpa only [abs_of_pos (softIndicator_positive K t x)] using hbound x)

lemma soft_smoothing_integral_tendsto {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D) {c : ℝ}
    (hc : 0 ≤ c) (y : E D) :
    Tendsto (fun j : ℕ => ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)
      atTop (𝓝 (∫ x in K, smoothingKernel A c y x)) := by
  have hcont : Continuous (smoothingKernel A c y) := continuous_smoothingKernel_right A c y
  have H := tendsto_integral_of_dominated_convergence (softIndicator K 1)
    (fun j => ((continuous_softIndicator K ((j : ℝ)+1)).mul hcont).aestronglyMeasurable)
    ((softIndicator_gaussianBound hK hne zero_lt_one).integrable (continuous_softIndicator K 1))
    (fun j => Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_pos (mul_pos (softIndicator_positive K _ x) (smoothingKernel_positive A c y x))]
      exact (mul_le_of_le_one_right (softIndicator_positive K _ x).le (smoothingKernel_le_one A hc y x)).trans
        (softIndicator_antitone K x (by nlinarith [Nat.cast_nonneg (α := ℝ) j] : (1:ℝ) ≤ (j : ℝ)+1))))
    (Filter.Eventually.of_forall (fun x => (softIndicator_tendsto hK.isClosed hne x).mul_const (smoothingKernel A c y x)))
  have he : (fun x => K.indicator (fun _ => (1:ℝ)) x*smoothingKernel A c y x)=
      K.indicator (smoothingKernel A c y) := by
    ext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [he,integral_indicator hK.measurableSet] at H
  exact H

lemma soft_smoothing_integral_inequality {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D)
    {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (y z : E D) (j : ℕ) :
    (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)^a*
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c z x)^b ≤
      ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c (a•y+b•z) x := by
  have hj : 0 < (j : ℝ)+1 := by positivity
  have hcont (v : E D) : Continuous (fun x => softIndicator K ((j : ℝ)+1) x*smoothingKernel A c v x) :=
    (continuous_softIndicator K _).mul (continuous_smoothingKernel_right A c v)
  have hpos (v : E D) (x : RV n) : 0 < softIndicator K ((j : ℝ)+1) x*smoothingKernel A c v x :=
    mul_pos (softIndicator_positive K _ x) (smoothingKernel_positive A c v x)
  apply gaussian_dominated_integral n (hcont y) (hcont z) (hcont _) (hpos y) (hpos z) (hpos _)
    (soft_smoothing_gaussianBound hK hne A hc hj y) (soft_smoothing_gaussianBound hK hne A hc hj z)
    (soft_smoothing_gaussianBound hK hne A hc hj _) ha hb hab
  intro u v
  rw [Real.mul_rpow (softIndicator_positive K _ u).le (smoothingKernel_positive A c y u).le,
    Real.mul_rpow (softIndicator_positive K _ v).le (smoothingKernel_positive A c z v).le]
  calc
    _ = (softIndicator K ((j : ℝ)+1) u^a*softIndicator K ((j : ℝ)+1) v^b)*
          (smoothingKernel A c y u^a*smoothingKernel A c z v^b) := by ring
    _ ≤ _ := mul_le_mul
      (softIndicator_weighted hK hK hne hne ha.le hb.le hab hj.le
        (fun u hu v hv => hconv hu hv ha.le hb.le hab) u v)
      (smoothingKernel_weighted A hc ha.le hb.le hab y z u v)
      (mul_nonneg (Real.rpow_nonneg (smoothingKernel_positive A c y u).le _)
        (Real.rpow_nonneg (smoothingKernel_positive A c z v).le _))
      (softIndicator_positive K _ _).le




theorem logConcave_smoothed_volume {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (A : RV n →ₗ[ℝ] E D)
    {c : ℝ} (hc : 0 ≤ c) :
    LogConcave (fun y => ∫ x in K, smoothingKernel A c y x) := by
  refine ⟨fun y => integral_nonneg (fun x => (smoothingKernel_positive A c y x).le),?_⟩
  intro y z a b ha hb hab
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb)]
  have hpoint : ∀ j : ℕ,
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)^a*
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c z x)^b ≤
      ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c (a•y+b•z) x := by
    exact soft_smoothing_integral_inequality hK hconv hne A hc ha hb hab y z
  exact le_of_tendsto_of_tendsto
    (((Real.continuous_rpow_const ha.le).tendsto _).comp (soft_smoothing_integral_tendsto hK hne A hc y) |>.mul
      (((Real.continuous_rpow_const hb.le).tendsto _).comp (soft_smoothing_integral_tendsto hK hne A hc z)))
    (soft_smoothing_integral_tendsto hK hne A hc _) (Filter.Eventually.of_forall hpoint)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma tail_quantiles_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1) :
    (3:ℝ)/4 ≤ μ.real {x | -2 ≤ X x} ∧ μ.real {x | 2 ≤ X x} ≤ (1:ℝ)/4 := by
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg (X x))) hi (4:ℝ)
  have htail : μ.real {x | 4 ≤ (X x)^2} ≤ (1:ℝ)/4 := by linarith
  constructor
  · have hc : {x | -2 ≤ X x}ᶜ ⊆ {x | 4 ≤ (X x)^2} := by
      intro x hx
      have hh : X x < -2 := lt_of_not_ge hx
      change 4 ≤ (X x)^2
      nlinarith [sq_nonneg (X x+2)]
    have hh := measureReal_mono (μ := μ) hc
    rw [probReal_compl_eq_one_sub (measurableSet_le measurable_const hX)] at hh
    linarith
  · apply le_trans (measureReal_mono ?_) htail
    intro x hx
    change 4 ≤ (X x)^2
    change 2 ≤ X x at hx
    nlinarith [sq_nonneg (X x-2)]

lemma scalar_tail_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hlc : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    {t : ℝ} (ht : 0 ≤ t) : μ.real {x | t ≤ X x} ≤ Real.exp (1-t/16) := by
  obtain ⟨hl,hr⟩ := tail_quantiles_of_second_moment μ hX hi h2
  exact hlc.exponential_tail (fun _ => measureReal_le_one) hl hr ht

lemma scalar_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hp : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    (hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -X x}))
    {t : ℝ} (ht : 0 ≤ t) : μ.real {x | t ≤ |X x|} ≤ 2*Real.exp (1-t/16) := by
  have hp' := scalar_tail_of_second_moment μ hX hi h2 hp ht
  have hn' := scalar_tail_of_second_moment μ hX.neg
    (by simpa only [Pi.neg_apply, neg_sq] using hi) (by simpa only [Pi.neg_apply, neg_sq] using h2) hn ht
  simp only [Pi.neg_apply] at hn'
  have hh : {x | t ≤ |X x|} = {x | t ≤ X x} ∪ {x | t ≤ -X x} := by
    ext x
    simp only [mem_ofPred_eq,mem_union,le_abs]
  rw [hh]
  exact (measureReal_union_le _ _).trans (by linarith)


lemma lintegral_fourth_eq_tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) :
    (∫⁻ x, ENNReal.ofReal ((X x)^4) ∂μ)=
      ∫⁻ t in Ioi (0:ℝ), μ {x | t ≤ |X x|}*ENNReal.ofReal (4*t^3) := by
  have H := lintegral_comp_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall (fun x => abs_nonneg (X x))) hX.abs.aemeasurable
    (g := fun t : ℝ => 4*t^3) (fun t ht => (by fun_prop : Continuous (fun t : ℝ => 4*t^3)).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt ht) _))
  have he (x : Ω) : (∫ t in (0:ℝ)..|X x|, 4*t^3)=(X x)^4 := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    norm_num
    rw [Even.pow_abs (by decide : Even (4:ℕ)) (X x)]
    ring
  simpa only [he] using H

noncomputable def fourthMomentConstant : ℝ := 8*Real.exp 1*16^4*6

lemma fourth_weight_integrable : IntegrableOn (fun t : ℝ => t^3*Real.exp (-(1/16:ℝ)*t)) (Ioi 0) volume := by
  have H := integrableOn_rpow_mul_exp_neg_mul_rpow
    (show (-1:ℝ) < 3 by norm_num) (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < 1/16 by norm_num)
  simpa only [Real.rpow_one,Real.rpow_ofNat] using H

lemma fourth_weight_integral :
    (∫ t : ℝ in Ioi 0, t^3*Real.exp (-(1/16:ℝ)*t))=(16:ℝ)^4*6 := by
  have H := Real.integral_rpow_mul_exp_neg_mul_Ioi (show (0:ℝ) < 4 by norm_num) (show (0:ℝ) < 1/16 by norm_num)
  have hg : Real.Gamma 4=6 := by norm_num
  norm_num only [show (4:ℝ)-1=3 by norm_num,Real.rpow_ofNat,hg,show (1:ℝ)/(1/16)=16 by norm_num] at H
  simpa only [neg_mul,show (16:ℝ)^4*6=393216 by norm_num] using H

lemma lintegral_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | t ≤ |X x|} ≤ 2*Real.exp (1-t/16)) :
    (∫⁻ x, ENNReal.ofReal ((X x)^4) ∂μ) ≤ ENNReal.ofReal fourthMomentConstant := by
  rw [lintegral_fourth_eq_tails μ hX]
  have he (t : ℝ) : (2*Real.exp (1-t/16))*(4*t^3)=(8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t)) := by
    rw [show 1-t/16=1+(-(1/16:ℝ)*t) by ring,Real.exp_add]
    ring
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [←he]
      rw [ENNReal.ofReal_mul (show 0 ≤ 2*Real.exp (1-t/16) by positivity)]
      apply mul_le_mul_left
      rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (htail t (le_of_lt ht))
    _ = ENNReal.ofReal (∫ t in Ioi (0:ℝ), (8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (fourth_weight_integrable.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
    _ = _ := by rw [integral_const_mul,fourth_weight_integral]; congr 1; unfold fourthMomentConstant; ring

lemma fourth_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hp : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    (hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -X x})) :
    Integrable (fun x => (X x)^4) μ ∧ (∫ x, (X x)^4 ∂μ) ≤ fourthMomentConstant := by
  have H := lintegral_fourth_le μ hX (fun t ht => scalar_abs_tail μ hX hi h2 hp hn ht)
  have hint : Integrable (fun x => (X x)^4) μ := by
    refine ⟨(hX.pow_const 4).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (show 0 ≤ (X x)^4 by positivity)))]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => by positivity))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (by unfold fourthMomentConstant; positivity)).mp H



end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
