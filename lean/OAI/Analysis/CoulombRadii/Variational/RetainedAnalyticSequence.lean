import Mathlib
import OAI.Analysis.CoulombRadii.Variational.PuncturedPosition

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem tfDensityScalar_nonneg (t : ℝ) : 0 ≤ tfDensityScalar t :=
  mul_nonneg kTF_pos.le (Real.rpow_nonneg (le_max_right t 0) _)

theorem tfDensityScalar_monotone : Monotone tfDensityScalar := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right s 0) (max_le_max_right 0 hst) (by norm_num)) kTF_pos.le

theorem tfReaction_dilate {D : ℝ} (hD : 0 < D) (t : ℝ) :
    tfReaction (D^4*t) = D^6*tfReaction t := by
  have hm : max (D^4*t) 0 = D^4*max t 0 := by
    rw [mul_max_of_nonneg t 0 (pow_nonneg hD.le 4), mul_zero]
  have hr : (D^4)^(3/2 : ℝ) = D^6 := by
    rw [← Real.rpow_natCast D 4, ← Real.rpow_mul hD.le]
    norm_num
  rw [tfReaction, hm, Real.mul_rpow (pow_nonneg hD.le 4) (le_max_right t 0), hr, tfReaction]
  ring

theorem semilinear_dilate {F : Position → ℝ} {D : ℝ} (hD : 0 < D)
    (hw : HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x))) :
    HasWeakLaplacian (fun x => D^4*F (D • x)) {x | x ≠ 0}
      (fun x => tfReaction (D^4*F (D • x))) := by
  have hh := hw.dilate hD
  have hU : ((fun x : Position => D • x) ⁻¹' {x | x ≠ 0}) = {x | x ≠ 0} := by
    ext x
    change D • x ≠ 0 ↔ x ≠ 0
    exact ⟨fun hx => (smul_ne_zero_iff.mp hx).2, fun hx => smul_ne_zero hD.ne' hx⟩
  rw [hU] at hh
  simpa only [tfReaction_dilate hD] using hh

theorem continuousOn_dilate {F : Position → ℝ} {D : ℝ} (hD : 0 < D)
    (hF : ContinuousOn F {x | x ≠ 0}) :
    ContinuousOn (fun x => D^4*F (D • x)) {x | x ≠ 0} := by
  apply continuousOn_const.mul
  exact hF.comp (continuous_id.const_smul D).continuousOn
    (fun x hx => smul_ne_zero hD.ne' hx)

theorem dilate_cap {F : Position → ℝ} {D C : ℝ} (hD : 0 < D)
    (hcap : ∀ x ≠ 0, F x ≤ C/‖x‖^4) :
    ∀ x ≠ 0, D^4*F (D • x) ≤ C/‖x‖^4 := by
  intro x hx
  calc
    D^4*F (D • x) ≤ D^4*(C/‖D • x‖^4) :=
      mul_le_mul_of_nonneg_left (hcap _ (smul_ne_zero hD.ne' hx)) (pow_nonneg hD.le 4)
    _ = C/‖x‖^4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD]
      field_simp

theorem semilinear_absolute_bound {F : Position → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ContinuousOn F {x | x ≠ 0})
    (hw : HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x)))
    (hcap : ∀ x ≠ 0, F x ≤ C/‖x‖^4)
    (hL : ∀ a b : ℝ, 0 < a → (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4 := by
  let V := closedNormAnnulus (1/2) 2
  let A := tfDensityScalar (C/(1/2)^4)
  let M := 2*(C/(1/2)^4)*(volume V).toReal
  have hA : 0 ≤ A := tfDensityScalar_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨K, hK, hest⟩ := poisson_interior_estimates_uniform
    (r := 1/8) (by norm_num) hA hM
  have hunit : ∀ D : ℝ, 0 < D → ∀ c : Position, ‖c‖ = 1 → ‖D^4*F (D • c)‖ ≤ K := by
    intro D hD c hc
    let G : Position → ℝ := fun x => D^4*F (D • x)
    let σ : Position → ℝ := fun x => tfDensityScalar (G x)
    have hc0 : c ≠ 0 := by intro he; simp only [he, norm_zero] at hc; norm_num at hc
    have hsub : Metric.closedBall c (3*(1/8)) ⊆ V := by
      simpa only [hc, one_div, V, closedNormAnnulus, mul_one] using closedBall_eighth_subset_annulus hc0
    have hV : V ⊆ {x : Position | x ≠ 0} := by
      intro x hx hz
      have hh := hx.1
      rw [hz, norm_zero] at hh
      norm_num at hh
    have h3 : Metric.ball c (3*(1/8)) ⊆ {x : Position | x ≠ 0} :=
      (Metric.ball_subset_closedBall.trans hsub).trans hV
    have h2 : Metric.ball c (2*(1/8)) ⊆ {x : Position | x ≠ 0} :=
      (Metric.ball_subset_ball (by norm_num : (2:ℝ)*(1/8) ≤ 3*(1/8))).trans h3
    have hCB : Metric.closedBall c (2*(1/8)) ⊆ V :=
      (Metric.closedBall_subset_closedBall (by norm_num : (2:ℝ)*(1/8) ≤ 3*(1/8))).trans hsub
    have hGc : ContinuousOn G {x | x ≠ 0} := continuousOn_dilate hD hF
    have hσc : ContinuousOn σ {x | x ≠ 0} := tfDensityScalar_continuous.comp_continuousOn hGc
    have hσi : IntegrableOn σ (Metric.closedBall c (3*(1/8))) :=
      (hσc.mono (hsub.trans hV)).integrableOn_compact (isCompact_closedBall _ _)
    have hσp : ∀ x ∈ Metric.closedBall c (3*(1/8)), 0 ≤ σ x :=
      fun x _ => tfDensityScalar_nonneg _
    have hσbd : ∀ x ∈ Metric.closedBall c (3*(1/8)), σ x ≤ A := by
      intro x hx
      apply tfDensityScalar_monotone
      exact (dilate_cap hD hcap x (hV (hsub hx))).trans
        (div_le_div_of_nonneg_left hC (by norm_num)
          (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (hsub hx).1 4))
    have hGw : HasWeakLaplacian G (Metric.ball c (2*(1/8))) (fun x => 4*Real.pi*σ x) := by
      have hh := (semilinear_dilate hD hw).mono h2
      convert hh using 1
      funext x
      simp only [σ, G, tfDensityScalar, tfReaction]
      ring
    have hIF : (∫ x in Metric.closedBall c (2*(1/8)), ‖G x‖) ≤ M := by
      calc
        (∫ x in Metric.closedBall c (2*(1/8)), ‖G x‖) ≤ ∫ x in V, ‖G x‖ :=
          setIntegral_mono_set ((hGc.mono hV).norm.integrableOn_compact
            (isCompact_closedNormAnnulus _ _)) (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (Filter.Eventually.of_forall hCB)
        _ ≤ M := dilate_annular_lone_bound hD (by norm_num : (0:ℝ)<1/2)
          (hL (D*(1/2)) (D*2) (by positivity))
    exact (hest c G σ (hGc.mono h3) hGw hσi hσp hσbd hIF).1 c
      (Metric.mem_closedBall_self (by norm_num))
  refine ⟨K,hK,?_⟩
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let c : Position := ‖x‖⁻¹ • x
  have hc : ‖c‖ = 1 := by
    change ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have he : ‖x‖ • c = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hb := hunit ‖x‖ hn c hc
  rw [he, norm_mul, Real.norm_eq_abs (‖x‖^4), abs_of_nonneg (pow_nonneg hn.le 4)] at hb
  exact (le_div_iff₀ (pow_pos hn 4)).mpr (by simpa only [mul_comm] using hb)

theorem eventual_barrier_boundary
    {Fn Un Ln : ℕ → Position → ℝ} {F : Position → ℝ} {a : ℕ → ℝ}
    {Cinv K S : ℝ} (hS : 0 < S)
    (hu : TendstoLocallyUniformlyOn Fn F atTop {x | x ≠ 0})
    (ha : Tendsto a atTop (𝓝 0))
    (hF : ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4)
    (hU : ∀ n x, a n ≤ ‖x‖ → Un n x ≤ Cinv/‖x‖^4)
    (hL : ∀ n x, 0 ≤ Ln n x) :
    ∀ᶠ n in atTop, ∀ x : Position, ‖x‖ = S →
      Un n x-Fn n x-Ln n x-(Cinv+K+1)/S^4 ≤ 0 := by
  have hsub : Metric.sphere (0 : Position) S ⊆ {x | x ≠ 0} := by
    intro x hx hz
    have hh : ‖x‖ = S := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    subst x
    simp only [norm_zero] at hh
    linarith
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0 : Position) S)).mp (hu.mono hsub)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') (1/S^4) (by positivity),
    ha.eventually (gt_mem_nhds hS)] with n hn han x hx
  have hxs : x ∈ Metric.sphere (0 : Position) S := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hx0 := hsub hxs
  have he : ‖Fn n x-F x‖ ≤ 1/S^4 := by
    simpa only [dist_comm, dist_eq_norm] using (hn x hxs).le
  have hfn : ‖Fn n x‖ ≤ (K+1)/S^4 := by
    calc
      ‖Fn n x‖ ≤ ‖Fn n x-F x‖+‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1/S^4+K/S^4 := add_le_add he (by simpa only [hx] using hF x hx0)
      _ = (K+1)/S^4 := by ring
  have hus : Un n x ≤ Cinv/S^4 := by
    simpa only [hx] using hU n x (by rw [hx]; exact han.le)
  have hneg : -Fn n x ≤ ‖Fn n x‖ := by simpa only [Real.norm_eq_abs] using neg_le_abs (Fn n x)
  have hls := hL n x
  have hc : (Cinv+K+1)/S^4 = Cinv/S^4+(K+1)/S^4 := by ring
  rw [hc]
  linarith

theorem barrier_lower_of_eventual_comparison
    {Fn Un : ℕ → Position → ℝ} {Ln : ℝ → ℕ → Position → ℝ}
    {F : Position → ℝ} {a : ℕ → ℝ} {B H : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (hF : ∀ x ≠ 0, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (hL : ∀ S x, x ≠ 0 → Tendsto (fun n => Ln S n x) atTop (𝓝 0))
    (hU : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ Un n x)
    (hcmp : ∀ S : ℝ, 0 < S → ∀ᶠ n in atTop,
      ∀ x ∈ Metric.closedBall (0 : Position) S, Un n x ≤ Fn n x+Ln S n x+H/S^4) :
    ∀ x ≠ 0, B/‖x‖^4 ≤ F x := by
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : ∀ S : ℝ, ‖x‖ < S → B/‖x‖^4 ≤ F x+H/S^4 := by
    intro S hS
    have hal : ∀ᶠ n in atTop, a n ≤ ‖x‖ :=
      (ha.eventually (gt_mem_nhds hn)).mono (fun n h => h.le)
    have ht1 : Tendsto (fun n => B/‖x‖^4*(1-a n/(8*‖x‖))) atTop (𝓝 (B/‖x‖^4)) := by
      simpa only [zero_div, sub_zero, mul_one] using
        (((tendsto_const_nhds (x := (1 : ℝ))).sub (ha.div_const (8*‖x‖))).const_mul (B/‖x‖^4))
    have ht2 : Tendsto (fun n => Fn n x+Ln S n x+H/S^4) atTop (𝓝 (F x+H/S^4)) := by
      simpa only [add_zero] using ((hF x hx).add (hL S x hx)).add_const (H/S^4)
    apply le_of_tendsto_of_tendsto ht1 ht2
    filter_upwards [hal, hcmp S (hn.trans hS)] with n han hcn
    exact (hU n x han).trans (hcn x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hS.le))
  have ht : Tendsto (fun S : ℝ => F x+H/S^4) atTop (𝓝 (F x)) := by
    have hh : Tendsto (fun S : ℝ => (S^4)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 4 ≠ 0))
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using (hh.const_mul H).const_add (F x)
  apply ge_of_tendsto ht
  exact (eventually_gt_atTop ‖x‖).mono (fun S hS => hb S hS)

theorem correctionDensity_bound {q a S : ℝ} (ha : 0 < a) (x : Position) :
    correctionDensity q a S x ≤ (q^8)⁻¹*(a^6)⁻¹ := by
  by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ S
  · have hx' : x ∈ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := hx
    rw [correctionDensity, Set.indicator_of_mem hx']
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos ha 6) (pow_le_pow_left₀ ha.le hx.1 6)) (by positivity : 0 ≤ (q^8)⁻¹)
  · have hx' : x ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := hx
    rw [correctionDensity, Set.indicator_of_notMem hx']
    positivity

theorem potentialOf_add_bounded {ρ η : Position → ℝ} {A B : ℝ}
    (hiρ : Integrable ρ) (hpρ : ∀ x, 0 ≤ ρ x) (hbρ : ∀ x, ρ x ≤ A)
    (hiη : Integrable η) (hpη : ∀ x, 0 ≤ η x) (hbη : ∀ x, η x ≤ B) (x : Position) :
    potentialOf (ρ+η) x = potentialOf ρ x+potentialOf η x := by
  have hi1 := (potential_integrable_and_bound (x := x) hiρ hpρ (by norm_num : (0:ℝ)<1)
    (fun y _ => hbρ y)).1
  have hi2 := (potential_integrable_and_bound (x := x) hiη hpη (by norm_num : (0:ℝ)<1)
    (fun y _ => hbη y)).1
  unfold potentialOf
  simp only [Pi.add_apply, mul_add]
  exact integral_add hi1 hi2

theorem full_correction_tendsto_zero {p : ℕ → Position → ℝ} {a q Ap : ℕ → ℝ}
    (hi : ∀ n, Integrable (p n)) (hp : ∀ n x, 0 ≤ p n x)
    (hb : ∀ n x, p n x ≤ Ap n) (hs : ∀ n x, a n < ‖x‖ → p n x = 0)
    (ha : Tendsto a atTop (𝓝 0)) (hap : ∀ n, 0 < a n)
    (hm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0))
    (hq : Tendsto q atTop atTop) (hal : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    (S : ℝ) {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (fun y => p n y+correctionDensity (q n) (a n) S y) x)
      atTop (𝓝 0) := by
  have hh := (inner_potential_tendsto_zero hi hp hs ha hm hx).add
    (correction_potential_tendsto_zero S hq hal hx)
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  exact potentialOf_add_bounded (hi n) (hp n) (hb n)
    (correctionDensity_integrable_and_mass (hap n)).1 (correctionDensity_nonneg _ _ _)
    (correctionDensity_bound (hap n)) x

theorem screened_limit_positive
    {σ U p : ℕ → Position → ℝ} {lam a q Aσ Ap : ℕ → ℝ}
    {F : Position → ℝ} {B Cinv K : ℝ}
    (hσi : ∀ n, Integrable (σ n)) (hσp : ∀ n x, 0 ≤ σ n x)
    (hσb : ∀ n x, σ n x ≤ Aσ n)
    (hpi : ∀ n, Integrable (p n)) (hpp : ∀ n x, 0 ≤ p n x)
    (hpb : ∀ n x, p n x ≤ Ap n) (hps : ∀ n x, a n < ‖x‖ → p n x = 0)
    (hpm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0))
    (hap : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0))
    (hq : Tendsto q atTop atTop) (hal : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    (hUc : ∀ n, Continuous (fun x => U n x-lam n*coulombKernel x))
    (hUl : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n x)
    (hUu : ∀ n x, a n ≤ ‖x‖ → U n x ≤ Cinv/‖x‖^4)
    (hUw : ∀ n, WeakNuclearSubsolution (U n) (lam n) Set.univ (barrierSource (a n) (U n) (σ n) (p n)))
    (hband : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
      |σ n x-tfDensityScalar (screenedField (lam n) (σ n) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹)
    (hu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σ n)) F atTop {x | x ≠ 0})
    (hK : 0 ≤ K) (hF : ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4) :
    ∀ x ≠ 0, B/‖x‖^4 ≤ F x := by
  let L : ℝ → ℕ → Position → ℝ := fun S n =>
    potentialOf (fun y => p n y+correctionDensity (q n) (a n) S y)
  have hLpos : ∀ S n x, 0 ≤ L S n x := fun S n x =>
    potentialOf_nonneg (fun y => add_nonneg (hpp n y) (correctionDensity_nonneg _ _ _ y)) x
  have hUb : ∀ n x, a n ≤ ‖x‖ → U n x ≤ max Cinv 0/‖x‖^4 := by
    intro n x hx
    exact (hUu n x hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  apply barrier_lower_of_eventual_comparison (H := max Cinv 0+K+1) ha
    (fun x hx => hu.tendsto_at hx) (fun S x hx =>
      full_correction_tendsto_zero hpi hpp hpb hps ha hap hpm hq hal S hx) hUl
  intro S hS
  have hbdy := eventual_barrier_boundary (Ln := L S) hS hu ha hF hUb (hLpos S)
  filter_upwards [hbdy, hq.eventually (eventually_ge_atTop S)] with n hbn hqn
  have hAU : ∀ x, a n ≤ ‖x‖ → U n x ≤ max Cinv 0/(a n)^4 := by
    intro x hx
    exact (hUb n x hx).trans (div_le_div_of_nonneg_left (le_max_right _ _)
      (pow_pos (hap n) 4) (pow_le_pow_left₀ (hap n).le hx 4))
  have hbw : WeakNuclearSubsolution (U n) (lam n) (Metric.ball 0 S)
      (barrierSource (a n) (U n) (σ n) (p n)) := by
    intro φ hφ hc ht hp
    exact hUw n φ hφ hc (fun _ _ => Set.mem_univ _) hp
  apply positive_barrier_comparison (hap n) hS (by positivity) (hUc n) hAU
    (hσi n) (hσp n) (hσb n) (hpi n) (hpp n) (hpb n)
    (correctionDensity_integrable_and_mass (hap n)).1
    (correctionDensity_nonneg _ _ _) (correctionDensity_bound (hap n)) hbw
  · intro x hx hax
    have hxS : ‖x‖ ≤ S := by
      exact (show ‖x‖ < S by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    have hb := (le_abs_self _).trans (hband n x hax (hxS.trans hqn))
    have heq : correctionDensity (q n) (a n) S x = ((q n)^8)⁻¹*(‖x‖^6)⁻¹ := by
      exact Set.indicator_of_mem (show x ∈ {y : Position | a n ≤ ‖y‖ ∧ ‖y‖ ≤ S} from ⟨hax,hxS⟩) _
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4*Real.pi)
    dsimp only [tfReaction, tfDensityScalar, screenedField, screenedPotential] at hh ⊢
    nlinarith only [hh]
  · exact hbn

theorem expanding_annular_error_locallyUniform
    {e : ℕ → Position → ℝ} {a q : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hband : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → |e n x| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹) :
    TendstoLocallyUniformlyOn e (fun _ => 0) atTop {x | x ≠ 0} := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨Metric.ball x (‖x‖/4), mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (by positivity)), ?_⟩
  have hq8 : Tendsto (fun n => ((q n)^8)⁻¹*((‖x‖/2)^6)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 8 ≠ 0)).comp hq)).mul_const (((‖x‖/2)^6)⁻¹)
  filter_upwards [ha.eventually (gt_mem_nhds (half_pos hn)),
    hq.eventually (eventually_ge_atTop (2*‖x‖)), hq8.eventually (gt_mem_nhds hε)] with n han hqn hen y hy
  have hy' : ‖x-y‖ < ‖x‖/4 := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hyl : ‖x‖/2 ≤ ‖y‖ := by linarith [norm_le_norm_sub_add x y]
  have hyu : ‖y‖ ≤ 2*‖x‖ := by
    have hh := norm_le_norm_sub_add y x
    rw [norm_sub_rev] at hh
    linarith
  have hh := hband n y (han.le.trans hyl) (hyu.trans hqn)
  have hinv := inv_anti₀ (pow_pos (half_pos hn) 6) (pow_le_pow_left₀ (half_pos hn).le hyl 6)
  have hle := hh.trans (mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ ((q n)^8)⁻¹))
  simpa only [dist_zero_left, Real.norm_eq_abs] using hle.trans_lt hen

theorem expanding_annular_cap_limit {Fn : ℕ → Position → ℝ} {F : Position → ℝ}
    {a q : ℕ → ℝ} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4)
    (hu : TendstoLocallyUniformlyOn Fn F atTop {x | x ≠ 0}) :
    ∀ x ≠ 0, F x ≤ C/‖x‖^4 := by
  intro x hx
  apply le_of_tendsto (hu.tendsto_at hx)
  filter_upwards [ha.eventually (gt_mem_nhds (norm_pos_iff.mpr hx)),
    hq.eventually (eventually_ge_atTop ‖x‖)] with n han hqn
  exact hcap n x han.le hqn

theorem expanding_annular_cap_eventually {Fn : ℕ → Position → ℝ}
    {a q : ℕ → ℝ} {C d r : ℝ} (hd : 0 < d)
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4) :
    ∀ᶠ n in atTop, ∀ x : Position, d ≤ ‖x‖ → ‖x‖ ≤ r → Fn n x ≤ C/‖x‖^4 := by
  filter_upwards [ha.eventually (gt_mem_nhds hd), hq.eventually (eventually_ge_atTop r)] with n han hqn x hxd hxr
  exact hcap n x (han.le.trans hxd) (hxr.trans hqn)

theorem expanding_annular_density_bound
    {Fn σ : ℕ → Position → ℝ} {a q : ℕ → ℝ} {C d r : ℝ} {f : ℝ → ℝ}
    (hf : Monotone f) (hfp : ∀ t, 0 ≤ f t) (hC : 0 ≤ C) (hd : 0 < d)
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4)
    (herr : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → |σ n x-f (Fn n x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ x : Position, d ≤ ‖x‖ → ‖x‖ ≤ r →
      Fn n x ≤ C/‖x‖^4 ∧ σ n x ≤ A := by
  refine ⟨f (C/d^4)+(d^6)⁻¹, add_nonneg (hfp _) (by positivity), ?_⟩
  filter_upwards [ha.eventually (gt_mem_nhds hd), hq.eventually (eventually_ge_atTop r),
    hq.eventually (eventually_ge_atTop 1)] with n han hqn hq1 x hxd hxr
  have hax := han.le.trans hxd
  have hxq := hxr.trans hqn
  have hfc := hcap n x hax hxq
  refine ⟨hfc, ?_⟩
  have hff := hf (hfc.trans (div_le_div_of_nonneg_left hC (pow_pos hd 4)
    (pow_le_pow_left₀ hd.le hxd 4)))
  have invq : ((q n)^8)⁻¹ ≤ 1 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1) (show (1:ℝ) ≤ (q n)^8 from one_le_pow₀ hq1)
    simpa only [inv_one] using hh
  have hinv := inv_anti₀ (pow_pos hd 6) (pow_le_pow_left₀ hd.le hxd 6)
  have he := (le_abs_self _).trans (herr n x hax hxq)
  have hle : ((q n)^8)⁻¹*(‖x‖^6)⁻¹ ≤ (d^6)⁻¹ := by
    exact (mul_le_mul_of_nonneg_left hinv (by positivity)).trans (by nlinarith [inv_nonneg.mpr (pow_nonneg hd.le 6)])
  linarith

theorem locallyUniform_of_subsequence
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [UniformSpace Y]
    {U : Set X} (hU : IsOpen U) {f : ℕ → X → Y} {g : X → Y}
    (hc : ∀ n, ContinuousOn (f n) U) (hg : ContinuousOn g U)
    (hsub : ∀ u : ℕ → ℕ, Tendsto u atTop atTop → ∃ v : ℕ → ℕ,
      TendstoLocallyUniformlyOn (fun n => f (u (v n))) g atTop U) :
    TendstoLocallyUniformlyOn f g atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let F : ℕ → C(U,Y) := fun n => ⟨fun x => f n x, continuousOn_iff_continuous_domRestrict.mp (hc n)⟩
  let G : C(U,Y) := ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
  change TendstoLocallyUniformly (fun n x => F n x) G atTop
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
  apply tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨v,hv⟩ := hsub u hu
  refine ⟨v, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr ?_⟩
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hv

structure RetainedAnalyticSequence where
  σ : ℕ → Position → ℝ
  U : ℕ → Position → ℝ
  p : ℕ → Position → ℝ
  lam : ℕ → ℝ
  a : ℕ → ℝ
  q : ℕ → ℝ
  Aσ : ℕ → ℝ
  Ap : ℕ → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  σi : ∀ n, Integrable (σ n)
  σp : ∀ n x, 0 ≤ σ n x
  σb : ∀ n x, σ n x ≤ Aσ n
  σmass : ∀ n, (∫ x, σ n x) = lam n
  pi : ∀ n, Integrable (p n)
  pp : ∀ n x, 0 ≤ p n x
  pb : ∀ n x, p n x ≤ Ap n
  ps : ∀ n x, a n < ‖x‖ → p n x = 0
  pm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0)
  apos : ∀ n, 0 < a n
  alim : Tendsto a atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  aq : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n
  Ucont : ∀ n, Continuous (fun x => U n x-lam n*coulombKernel x)
  Ulower : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n x
  Uupper : ∀ n x, a n ≤ ‖x‖ → U n x ≤ Cinv/‖x‖^4
  Uweak : ∀ n, WeakNuclearSubsolution (U n) (lam n) Set.univ (barrierSource (a n) (U n) (σ n) (p n))
  cap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → screenedField (lam n) (σ n) x ≤ Ccap/‖x‖^4
  err : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
    |σ n x-tfDensityScalar (screenedField (lam n) (σ n) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹

end NeutralAtom
end
end

end OAI
