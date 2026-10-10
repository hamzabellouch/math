import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.TfReaction
import OAI.Analysis.CoulombRadii.RadialBounds.Radial

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem closedBall_eighth_subset_annulus {c : Position} (hc : c ≠ 0) :
    Metric.closedBall c (3*(‖c‖/8)) ⊆ {x : Position | ‖c‖/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*‖c‖} := by
  intro x hx
  change dist x c ≤ 3*(‖c‖/8) at hx
  rw [dist_eq_norm] at hx
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 := norm_sub_norm_le x c
  have h2 := norm_sub_norm_le c x
  rw [norm_sub_rev] at h2
  constructor <;> linarith

theorem neutral_screened_ball_estimates {c : Position} (hc : c ≠ 0) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ (lam Aσ : ℝ) (σ : Position → ℝ),
      Integrable σ → (∀ x, 0 ≤ σ x) → (∀ x, σ x ≤ Aσ) → (∫ x, σ x) = lam →
      (∀ x : Position, ‖c‖/2 ≤ ‖x‖ → ‖x‖ ≤ 2*‖c‖ →
        screenedField lam σ x ≤ C/‖x‖^4 ∧ σ x ≤ A) →
      (∀ z ∈ Metric.closedBall c (‖c‖/8), ‖screenedField lam σ z‖ ≤ D) ∧
      (∀ z ∈ Metric.closedBall c (‖c‖/8), ∀ z' ∈ Metric.closedBall c (‖c‖/8),
        ‖screenedField lam σ z-screenedField lam σ z'‖ ≤ D*‖z-z'‖) := by
  let r := ‖c‖/8
  let V := {x : Position | ‖c‖/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*‖c‖}
  let M := 2*(C/(‖c‖/2)^4)*(volume V).toReal
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 < r := by dsimp [r]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨D, hD, hest⟩ := poisson_interior_estimates c hr hA hM
  refine ⟨D, hD, ?_⟩
  intro lam Aσ σ hi hp hb hm hcap
  have hsub : Metric.closedBall c (3*r) ⊆ V := closedBall_eighth_subset_annulus hc
  have hV : V ⊆ {x : Position | x ≠ 0} := by
    intro x hx hz
    have hh := hx.1
    rw [hz, norm_zero] at hh
    linarith
  have h3 : Metric.ball c (3*r) ⊆ {x : Position | x ≠ 0} :=
    (Metric.ball_subset_closedBall.trans hsub).trans hV
  have h2 : Metric.ball c (2*r) ⊆ {x : Position | x ≠ 0} :=
    (Metric.ball_subset_ball (by linarith : 2*r ≤ 3*r)).trans h3
  have hCB : Metric.closedBall c (2*r) ⊆ V :=
    (Metric.closedBall_subset_closedBall (by linarith : 2*r ≤ 3*r)).trans hsub
  have hcont := screenedField_continuousOn hi hp hb (lam := lam)
  apply hest (screenedField lam σ) σ (hcont.mono h3)
    ((screenedField_weakLaplacian hi hp hb).mono h2) hi hp
    (fun x hx => (hcap x (hsub hx).1 (hsub hx).2).2)
  have hint : IntegrableOn (fun x => ‖screenedField lam σ x‖) V :=
    (hcont.mono hV).norm.integrableOn_compact (isCompact_closedNormAnnulus _ _)
  calc
    (∫ x in Metric.closedBall c (2*r), ‖screenedField lam σ x‖) ≤
        ∫ x in V, ‖screenedField lam σ x‖ :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall (fun x => norm_nonneg _))
        (Filter.Eventually.of_forall hCB)
    _ ≤ M := by
      exact neutral_annulus_lone_bound hi hp hb hm (by positivity) hC
        (fun x hxa hxb => (hcap x hxa hxb).1)

abbrev PuncturedPosition := {x : Position // x ≠ 0}

def extendPunctured (f : PuncturedPosition → ℝ) (x : Position) : ℝ :=
  if hx : x ≠ 0 then f ⟨x, hx⟩ else 0

@[simp] theorem extendPunctured_val (f : PuncturedPosition → ℝ) (x : PuncturedPosition) :
    extendPunctured f x = f x := by simp [extendPunctured, x.property]

theorem neutral_screened_precompact_sequence
    {σ : ℕ → Position → ℝ} {lam Aσ : ℕ → ℝ} {C : ℝ}
    (hσi : ∀ n, Integrable (σ n)) (hσp : ∀ n x, 0 ≤ σ n x)
    (hσbd : ∀ n x, σ n x ≤ Aσ n) (hmass : ∀ n, (∫ x, σ n x) = lam n)
    (hC : 0 ≤ C)
    (hband : ∀ a b : ℝ, 0 < a → a < b → ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
        screenedField (lam n) (σ n) x ≤ C/‖x‖^4 ∧ σ n x ≤ A) :
    ∃ (F : Position → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ContinuousOn F {x | x ≠ 0} ∧
      TendstoLocallyUniformlyOn (fun n => screenedField (lam (φ n)) (σ (φ n))) F atTop {x | x ≠ 0} ∧
      LocallyLipschitzOn Set.univ (fun x : PuncturedPosition => F x) := by
  let : LocallyCompactSpace PuncturedPosition :=
    (isOpen_ne : IsOpen {x : Position | x ≠ 0}).locallyCompactSpace
  let G : ℕ → PuncturedPosition → ℝ := fun n x => screenedField (lam n) (σ n) x
  have hGc : ∀ n, Continuous (G n) := fun n =>
    continuousOn_iff_continuous_domRestrict.mp
      (screenedField_continuousOn (hσi n) (hσp n) (hσbd n))
  have hGe : ∀ x : PuncturedPosition, ∃ (r D : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ D ∧
      ∀ n, N ≤ n → ‖G n x‖ ≤ D ∧
        ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r, ‖G n y-G n z‖ ≤ D*dist y z := by
    intro x
    have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
    obtain ⟨A, hA, hEv⟩ := hband (‖x.val‖/2) (2*‖x.val‖) (by positivity) (by linarith)
    obtain ⟨D, hD, hEst⟩ := neutral_screened_ball_estimates x.property hC hA
    obtain ⟨N, hN⟩ := eventually_atTop.mp hEv
    refine ⟨‖x.val‖/8, D, N, by positivity, hD.le, ?_⟩
    intro n hn'
    obtain ⟨hv, hl⟩ := hEst (lam n) (Aσ n) (σ n) (hσi n) (hσp n) (hσbd n) (hmass n) (hN n hn')
    constructor
    · exact hv x (Metric.mem_closedBall_self (by positivity))
    · intro y hy z hz
      have hy' : y.val ∈ Metric.closedBall x.val (‖x.val‖/8) := Metric.mem_closedBall.mpr hy.le
      have hz' : z.val ∈ Metric.closedBall x.val (‖x.val‖/8) := Metric.mem_closedBall.mpr hz.le
      simpa only [G, Subtype.dist_eq, dist_eq_norm] using hl y hy' z hz'
  obtain ⟨f, φ, hφ, hu, hl⟩ := locallyUniform_subsequence_of_eventual_ball_estimates G hGc hGe
  refine ⟨extendPunctured f, φ, hφ, ?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : PuncturedPosition => extendPunctured f x)
    simpa only [extendPunctured_val] using f.continuous
  · apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    change TendstoLocallyUniformly (fun n (x : PuncturedPosition) =>
      screenedField (lam (φ n)) (σ (φ n)) x)
      (fun x : PuncturedPosition => extendPunctured f x) atTop
    simpa only [extendPunctured_val, G] using hu
  · simpa only [extendPunctured_val] using hl

theorem tendsto_integral_mul_test_of_locallyUniformlyOn
    {F : ℕ → Position → ℝ} {f ψ : Position → ℝ} {U : Set Position}
    (hF : ∀ n, LocallyIntegrableOn (F n) U) (hf : ContinuousOn f U)
    (hu : TendstoLocallyUniformlyOn F f atTop U)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (ht : tsupport ψ ⊆ U) :
    Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, f x * ψ x)) := by
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc).mp (hu.mono ht)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (hf.mono ht)
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ tsupport ψ, ‖F n x‖ ≤ max M 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') 1 (by norm_num)] with n hn x hx
    calc
      ‖F n x‖ ≤ ‖F n x-f x‖+‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+M := add_le_add (by simpa only [dist_comm, dist_eq_norm] using (hn x hx).le) (hM x hx)
      _ ≤ max M 0+1 := by linarith [le_max_left M 0]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (max M 0+1)*‖ψ x‖)
  · exact Filter.Eventually.of_forall fun n => (integrable_mul_test_on (hF n) hψ hc ht).aestronglyMeasurable
  · filter_upwards [hbd] with n hn
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport ψ
      · simpa only [norm_mul] using mul_le_mul_of_nonneg_right (hn x hx) (norm_nonneg (ψ x))
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero, le_refl]
  · exact (hψ.norm.integrable_of_hasCompactSupport hc.norm).const_mul _
  · exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport ψ
      · exact (hu'.tendsto_at hx).mul_const (ψ x)
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
        exact tendsto_const_nhds

theorem continuous_comp_locallyUniformlyOn
    {F : ℕ → Position → ℝ} {f : Position → ℝ} {U : Set Position} {g : ℝ → ℝ}
    (hu : TendstoLocallyUniformlyOn F f atTop U) (hf : ContinuousOn f U)
    (hg : Continuous g) :
    TendstoLocallyUniformlyOn (fun n x => g (F n x)) (fun x => g (f x)) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have hj : Tendsto (fun z : ℕ × Position => F z.1 z.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (f x)) := by
    apply tendsto_comp_of_locally_uniform_limit_within (hf x hx) tendsto_snd
    intro v hv
    obtain ⟨t, ht, hFt⟩ := hu v hv x hx
    exact ⟨t, ht, tendsto_fst.eventually hFt⟩
  have hf' : Tendsto (fun z : ℕ × Position => f z.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (f x)) := Filter.Tendsto.comp (hf x hx) tendsto_snd
  exact ((hg.continuousAt.tendsto.comp hf').prodMk_nhds
    (hg.continuousAt.tendsto.comp hj)).mono_right (nhds_le_uniformity _)

theorem HasWeakLaplacian.locallyUniformLimit
    {Fn qn : ℕ → Position → ℝ} {F q : Position → ℝ} {U : Set Position}
    (hU : IsOpen U) (hFc : ∀ n, ContinuousOn (Fn n) U)
    (hqc : ∀ n, LocallyIntegrableOn (qn n) U)
    (hF : ContinuousOn F U) (hq : ContinuousOn q U)
    (hFu : TendstoLocallyUniformlyOn Fn F atTop U)
    (hqu : TendstoLocallyUniformlyOn qn q atTop U)
    (hw : ∀ n, HasWeakLaplacian (Fn n) U (qn n)) : HasWeakLaplacian F U q := by
  intro φ hφ hc ht
  have hl := tendsto_integral_mul_test_of_locallyUniformlyOn
    (fun n => (hFc n).locallyIntegrableOn hU.measurableSet) hF hFu
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hc) ((tsupport_coordinateLaplacian_subset φ).trans ht)
  have hr := tendsto_integral_mul_test_of_locallyUniformlyOn hqc hq hqu hφ.continuous hc ht
  exact tendsto_nhds_unique
    (hl.congr' (Filter.Eventually.of_forall fun n => hw n φ hφ hc ht)) hr

def tfDensityScalar (t : ℝ) : ℝ := kTF*(max t 0)^(3/2 : ℝ)

theorem tfDensityScalar_continuous : Continuous tfDensityScalar := by
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    (continuous_id.max continuous_const))

theorem density_locallyUniform_of_vanishing_error
    {Fn σn : ℕ → Position → ℝ} {F : Position → ℝ} {U : Set Position}
    (hFu : TendstoLocallyUniformlyOn Fn F atTop U) (hF : ContinuousOn F U)
    (he : TendstoLocallyUniformlyOn (fun n x => σn n x-tfDensityScalar (Fn n x))
      (fun _ => 0) atTop U) :
    TendstoLocallyUniformlyOn σn (fun x => tfDensityScalar (F x)) atTop U := by
  have hh := he.add (continuous_comp_locallyUniformlyOn hFu hF tfDensityScalar_continuous)
  change TendstoLocallyUniformlyOn (fun n x => σn n x-tfDensityScalar (Fn n x)+tfDensityScalar (Fn n x))
    (fun x => 0+tfDensityScalar (F x)) atTop U at hh
  simpa only [sub_add_cancel, zero_add] using hh

theorem screened_semilinear_limit
    {σn : ℕ → Position → ℝ} {lam A : ℕ → ℝ} {F : Position → ℝ}
    (hσi : ∀ n, Integrable (σn n)) (hσp : ∀ n x, 0 ≤ σn n x)
    (hσbd : ∀ n x, σn n x ≤ A n)
    (hF : ContinuousOn F {x | x ≠ 0})
    (hFu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σn n)) F atTop {x | x ≠ 0})
    (he : TendstoLocallyUniformlyOn
      (fun n x => σn n x-tfDensityScalar (screenedField (lam n) (σn n) x))
      (fun _ => 0) atTop {x | x ≠ 0}) :
    HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x)) := by
  have hσu := density_locallyUniform_of_vanishing_error hFu hF he
  have hqu := continuous_comp_locallyUniformlyOn (g := fun t : ℝ => (4*Real.pi)*t) hσu
    (tfDensityScalar_continuous.comp_continuousOn hF) (continuous_const.mul continuous_id)
  have hqr : TendstoLocallyUniformlyOn (fun n x => (4*Real.pi)*σn n x)
      (fun x => tfReaction (F x)) atTop {x | x ≠ 0} := by
    convert hqu using 1
    funext x
    simp only [tfReaction, tfDensityScalar]
    ring
  exact HasWeakLaplacian.locallyUniformLimit isOpen_ne
    (fun n => screenedField_continuousOn (hσi n) (hσp n) (hσbd n))
    (fun n => ((hσi n).const_mul (4*Real.pi)).locallyIntegrable.locallyIntegrableOn _)
    hF (tfReaction_continuous.comp_continuousOn hF) hFu hqr
    (fun n => screenedField_weakLaplacian (hσi n) (hσp n) (hσbd n))

theorem poisson_interior_estimates_uniform {r A M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball c (3*r)) →
      HasWeakLaplacian F (Metric.ball c (2*r)) (fun x => 4*Real.pi*σ x) →
      IntegrableOn σ (Metric.closedBall c (3*r)) →
      (∀ x ∈ Metric.closedBall c (3*r), 0 ≤ σ x) →
      (∀ x ∈ Metric.closedBall c (3*r), σ x ≤ A) →
      (∫ x in Metric.closedBall c (2*r), ‖F x‖) ≤ M →
      (∀ z ∈ Metric.closedBall c r, ‖F z‖ ≤ C) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖F z-F z'‖ ≤ C*‖z-z'‖) := by
  obtain ⟨HC, hHC, hest⟩ := harmonic_interior_estimates_local hr
  let V := (volume (Metric.closedBall (0 : Position) (3*r))).toReal
  let V' := (volume (Metric.closedBall (0 : Position) (2*r))).toReal
  let PB := A*(∫ y in Metric.ball (0 : Position) 1, coulombKernel y)+A*V
  let LB := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+A*V
  have hPB : 0 ≤ PB := add_nonneg (mul_nonneg hA (integral_nonneg coulombKernel_nonneg))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  have hLB : 0 ≤ LB := add_nonneg (mul_nonneg hA (integral_nonneg (fun y => sq_nonneg _)))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  let H := M+PB*V'
  have hH : 0 ≤ H := add_nonneg hM (mul_nonneg hPB ENNReal.toReal_nonneg)
  let C := HC*H+PB+LB+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c F σ hF hpoisson hσ hσpos hσbd hIF
  let W := Metric.closedBall c (3*r)
  let W' := Metric.closedBall c (2*r)
  have hV : (volume W).toReal = V := by
    simp only [W, V, EuclideanSpace.volume_closedBall]
  have hV' : (volume W').toReal = V' := by
    simp only [W', V', EuclideanSpace.volume_closedBall]
  let ρ := W.indicator σ
  have hρ : Integrable ρ := (integrable_indicator_iff measurableSet_closedBall).mpr hσ
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => Set.indicator_nonneg hσpos x
  have hρbd : ∀ x, ρ x ≤ A := by
    intro x
    by_cases hx : x ∈ W
    · simpa only [ρ, Set.indicator_of_mem hx] using hσbd x hx
    · simpa only [ρ, Set.indicator_of_notMem hx] using hA
  have hmass : (∫ x, ρ x) ≤ A*V := by
    rw [show ρ = W.indicator σ from rfl, integral_indicator measurableSet_closedBall]
    calc
      (∫ x in W, σ x) ≤ ∫ _ in W, A := integral_mono_ae hσ
        (integrableOn_const (isCompact_closedBall c (3*r)).measure_ne_top)
        ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hσbd x hx))
      _ = A*V := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul,
          measureReal_def, hV, mul_comm]
  let P := potentialOf ρ
  have hPcont : Continuous P := potentialOf_continuous hρ hρpos hρbd
  have hPbd (x : Position) : ‖P x‖ ≤ PB := by
    have hp : 0 ≤ P x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρpos y))
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hρpos hρbd x).2.trans (by dsimp only [PB]; linarith)
  have hPlip (x y : Position) : ‖P x-P y‖ ≤ LB*‖x-y‖ :=
    (potentialOf_lipschitz_bound hρ hρpos hρbd x y).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [LB]; linarith) (norm_nonneg _))
  have hW' : W' ⊆ Metric.ball c (3*r) := by
    intro x hx
    change dist x c ≤ 2*r at hx
    change dist x c < 3*r
    linarith
  have hball : Metric.ball c (2*r) ⊆ Metric.ball c (3*r) :=
    Metric.ball_subset_ball (by linarith)
  let h : Position → ℝ := fun x => F x+P x
  have hhcont : ContinuousOn h (Metric.ball c (3*r)) := hF.add hPcont.continuousOn
  have hharm : HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) :=
    local_harmonic_part Metric.isOpen_ball (hF.mono hball) hpoisson hρ hρpos hρbd (by
      intro x hx
      have hxW : x ∈ W := by
        change dist x c ≤ 3*r
        exact (hball hx).le
      exact (Set.indicator_of_mem hxW σ).symm)
  have hiF : IntegrableOn (fun x => ‖F x‖) W' :=
    ((hF.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hih : IntegrableOn (fun x => ‖h x‖) W' :=
    ((hhcont.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hiPB : IntegrableOn (fun _ : Position => PB) W' :=
    integrableOn_const (isCompact_closedBall c (2*r)).measure_ne_top
  have hIh : (∫ x in W', ‖h x‖) ≤ H := by
    calc
      (∫ x in W', ‖h x‖) ≤ ∫ x in W', ‖F x‖+PB := integral_mono_ae hih (hiF.add hiPB)
        (Filter.Eventually.of_forall (fun x => (norm_add_le (F x) (P x)).trans
          (add_le_add le_rfl (hPbd x))))
      _ = (∫ x in W', ‖F x‖)+PB*V' := by
        rw [integral_add hiF hiPB, integral_const]
        simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def, hV', mul_comm]
      _ ≤ H := by dsimp only [H]; linarith
  obtain ⟨hval, hdiff⟩ := hest c h hhcont hharm
  have hCval : HC*H+PB ≤ C := by dsimp [C]; linarith
  have hClip : HC*H+LB ≤ C := by dsimp [C]; linarith
  constructor
  · intro z hz
    calc
      ‖F z‖ = ‖h z-P z‖ := by dsimp [h]; rw [add_sub_cancel_right]
      _ ≤ ‖h z‖+‖P z‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)+PB := add_le_add (hval z hz) (hPbd z)
      _ ≤ HC*H+PB := by linarith [mul_le_mul_of_nonneg_left hIh hHC.le]
      _ ≤ C := hCval
  · intro z hz z' hz'
    calc
      ‖F z-F z'‖ = ‖(h z-h z')-(P z-P z')‖ := by congr 1; dsimp [h]; ring
      _ ≤ ‖h z-h z'‖+‖P z-P z'‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)*‖z-z'‖+LB*‖z-z'‖ :=
        add_le_add (hdiff z hz z' hz') (hPlip z z')
      _ ≤ (HC*H+LB)*‖z-z'‖ := by
        have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIh hHC.le)
          (norm_nonneg (z-z'))
        nlinarith
      _ ≤ C*‖z-z'‖ := mul_le_mul_of_nonneg_right hClip (norm_nonneg _)

theorem tendsto_integral_norm_on_compact_of_locallyUniformlyOn
    {Fn : ℕ → Position → ℝ} {F : Position → ℝ} {U K : Set Position}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hFn : ∀ n, ContinuousOn (Fn n) U) (hF : ContinuousOn F U)
    (hu : TendstoLocallyUniformlyOn Fn F atTop U) :
    Tendsto (fun n => ∫ x in K, ‖Fn n x‖) atTop (𝓝 (∫ x in K, ‖F x‖)) := by
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hu.mono hKU)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF.mono hKU)
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ K, ‖Fn n x‖ ≤ max M 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') 1 (by norm_num)] with n hn x hx
    calc
      ‖Fn n x‖ ≤ ‖Fn n x-F x‖+‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+M := add_le_add (by simpa only [dist_comm, dist_eq_norm] using (hn x hx).le) (hM x hx)
      _ ≤ max M 0+1 := by linarith [le_max_left M 0]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => max M 0+1)
  · exact Filter.Eventually.of_forall fun n =>
      ((hFn n).mono hKU).norm.aestronglyMeasurable hK.measurableSet
  · filter_upwards [hbd] with n hn
    exact (ae_restrict_mem hK.measurableSet).mono fun x hx => by
      simpa only [norm_norm] using hn x hx
  · exact integrableOn_const hK.measure_ne_top
  · exact (ae_restrict_mem hK.measurableSet).mono fun x hx => (hu'.tendsto_at hx).norm

def closedNormAnnulus (a b : ℝ) : Set Position := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

theorem smul_closedNormAnnulus {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    D • closedNormAnnulus a b = closedNormAnnulus (D*a) (D*b) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hD.ne']
  simp only [closedNormAnnulus, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hD), ← div_eq_inv_mul]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hD).mp h1,
      by simpa only [mul_comm] using (div_le_iff₀ hD).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨(le_div_iff₀ hD).mpr (by simpa only [mul_comm] using h1),
      (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h2)⟩

theorem volume_closedNormAnnulus_dilate {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    (volume (closedNormAnnulus (D*a) (D*b))).toReal =
      D^3*(volume (closedNormAnnulus a b)).toReal := by
  have hh := Measure.setIntegral_comp_smul_of_pos volume (fun _ : Position => (1 : ℝ))
    (closedNormAnnulus a b) hD
  simp only [smul_closedNormAnnulus hD, Position, finrank_euclideanSpace_fin,
    integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def] at hh
  rw [hh]
  field_simp

theorem dilate_annular_lone_bound {F : Position → ℝ} {C D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a)
    (hL : (∫ x in closedNormAnnulus (D*a) (D*b), ‖F x‖) ≤
      2*(C/(D*a)^4)*(volume (closedNormAnnulus (D*a) (D*b))).toReal) :
    (∫ x in closedNormAnnulus a b, ‖D^4*F (D • x)‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
  simp_rw [norm_mul, Real.norm_eq_abs (D^4), abs_of_nonneg (pow_nonneg hD.le 4),
    integral_const_mul]
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖F x‖) (closedNormAnnulus a b) hD]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul, smul_closedNormAnnulus hD]
  calc
    D^4*((D^3)⁻¹*(∫ x in closedNormAnnulus (D*a) (D*b), ‖F x‖)) ≤
      D^4*((D^3)⁻¹*(2*(C/(D*a)^4)*(volume (closedNormAnnulus (D*a) (D*b))).toReal)) := by
        gcongr
    _ = 2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
      rw [volume_closedNormAnnulus_dilate hD]
      field_simp

theorem neutral_screened_limit_annular_lone
    {σn : ℕ → Position → ℝ} {lam A : ℕ → ℝ} {F : Position → ℝ} {C a b : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a)
    (hσi : ∀ n, Integrable (σn n)) (hσp : ∀ n x, 0 ≤ σn n x)
    (hσbd : ∀ n x, σn n x ≤ A n) (hmass : ∀ n, (∫ x, σn n x) = lam n)
    (hF : ContinuousOn F {x | x ≠ 0})
    (hFu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σn n)) F atTop {x | x ≠ 0})
    (hcap : ∀ᶠ n in atTop, ∀ x ∈ closedNormAnnulus a b,
      screenedField (lam n) (σn n) x ≤ C/‖x‖^4) :
    (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
  have hK : IsCompact (closedNormAnnulus a b) := isCompact_closedNormAnnulus a b
  have hKU : closedNormAnnulus a b ⊆ {x : Position | x ≠ 0} := by
    intro x hx hz
    have hh := hx.1
    rw [hz, norm_zero] at hh
    linarith
  have ht := tendsto_integral_norm_on_compact_of_locallyUniformlyOn hK hKU
    (fun n => screenedField_continuousOn (hσi n) (hσp n) (hσbd n)) hF hFu
  apply le_of_tendsto ht
  filter_upwards [hcap] with n hn
  exact neutral_annulus_lone_bound (hσi n) (hσp n) (hσbd n) (hmass n) ha hC
    (fun x hxa hxb => hn x ⟨hxa,hxb⟩)

end NeutralAtom
end
end

end OAI
