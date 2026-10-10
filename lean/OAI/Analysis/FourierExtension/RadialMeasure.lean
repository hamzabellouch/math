import Mathlib

namespace OAI

/-! Radial pushforward estimates for convex phases. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter
open scoped ENNReal InnerProductSpace
open scoped FourierTransform SchwartzMap ENNReal
open scoped ENNReal FourierTransform InnerProductSpace

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace DiagonalExtension.ConvexRadial

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def symPhase (φ : E2 → ℝ) (m dir : E2) (r : ℝ) : ℝ :=
  φ (m + r • dir) + φ (m - r • dir)

def symPhaseDeriv (φ : E2 → ℝ) (m dir : E2) (r : ℝ) : ℝ :=
  (fderiv ℝ φ (m + r • dir)) dir - (fderiv ℝ φ (m - r • dir)) dir

lemma hasDerivAt_line (m dir : E2) (r : ℝ) :
    HasDerivAt (fun s : ℝ => m + s • dir) dir r := by
  simpa only [one_smul, id_eq] using!
    ((hasDerivAt_id r).smul_const dir).const_add m

lemma hasDerivAt_line_sub (m dir : E2) (r : ℝ) :
    HasDerivAt (fun s : ℝ => m - s • dir) (-dir) r := by
  simpa only [one_smul, id_eq, sub_eq_add_neg] using!
    ((hasDerivAt_id r).smul_const dir).neg.const_add m

lemma hasDerivAt_symPhase {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (m dir : E2) (r : ℝ) :
    HasDerivAt (symPhase φ m dir) (symPhaseDeriv φ m dir r) r := by
  have hd := hφ.differentiable (by simp)
  simpa only [symPhase, symPhaseDeriv, map_neg, sub_eq_add_neg, Pi.add_apply, Function.comp_apply] using!
    ((hd (m + r • dir)).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_line m dir r)).add
      ((hd (m - r • dir)).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_line_sub m dir r))

lemma hasDerivAt_directional {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (m dir : E2) (r : ℝ) :
    HasDerivAt (fun s : ℝ => (fderiv ℝ φ (m + s • dir)) dir)
      ((fderiv ℝ (fderiv ℝ φ) (m + r • dir) dir) dir) r := by
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by exact WithTop.coe_le_coe.mpr (show (1 : ℕ∞) + 1 ≤ ⊤ from le_top))
  have hdf : Differentiable ℝ (fderiv ℝ φ) := hd.differentiable (by norm_num)
  have H₀ : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (m + r • dir))
      (m + r • dir) := (hdf (m + r • dir)).hasFDerivAt
  have H₁ : HasDerivAt (fun s : ℝ => fderiv ℝ φ (m + s • dir))
      (fderiv ℝ (fderiv ℝ φ) (m + r • dir) dir) r :=
    H₀.comp_hasDerivAt r (hasDerivAt_line m dir r)
  simpa only [map_zero, add_zero] using H₁.clm_apply (hasDerivAt_const r dir)

lemma radial_deriv_lower {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    (m : E2) {dir : E2} (hdir : ‖dir‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    2 * c * r ≤ symPhaseDeriv φ m dir r := by
  let F : ℝ → ℝ := fun s => (fderiv ℝ φ (m + s • dir)) dir
  have hF (s : ℝ) : HasDerivAt F
      ((fderiv ℝ (fderiv ℝ φ) (m + s • dir) dir) dir) s :=
    hasDerivAt_directional hφ m dir s
  have hc (s : ℝ) : c ≤ deriv F s := by
    rw [(hF s).deriv]
    simpa only [hdir, one_pow, mul_one] using hell (m + s • dir) dir
  have H := mul_sub_le_image_sub_of_le_deriv (fun s => (hF s).differentiableAt)
    hc (show -r ≤ r by linarith)
  simpa only [F, neg_smul, ← sub_eq_add_neg, symPhaseDeriv, sub_neg_eq_add,
    ← two_mul, mul_comm c, mul_assoc] using H

lemma symPhase_continuous {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (m dir : E2) :
    Continuous (symPhase φ m dir) :=
  continuous_iff_continuousAt.mpr (fun r => (hasDerivAt_symPhase hφ m dir r).continuousAt)

lemma symPhase_strictMonoOn {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    (m : E2) {dir : E2} (hdir : ‖dir‖ = 1) :
    StrictMonoOn (symPhase φ m dir) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (symPhase_continuous hφ m dir).continuousOn
  intro r hr
  rw [interior_Ici, mem_Ioi] at hr
  rw [(hasDerivAt_symPhase hφ m dir r).deriv]
  exact (mul_pos (mul_pos (by norm_num) hc) hr).trans_le
    (radial_deriv_lower hφ hell m hdir hr.le)

lemma radial_lintegral_le {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    (m : E2) {dir : E2} (hdir : ‖dir‖ = 1) (g : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g (symPhase φ m dir r) ≤
      ENNReal.ofReal ((2 * c)⁻¹) * ∫⁻ s : ℝ, g s := by
  have hc2 : 0 < 2 * c := mul_pos (by norm_num) hc
  have hmono := (symPhase_strictMonoOn hφ hc hell m hdir).mono Ioi_subset_Ici_self
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun r (_ : r ∈ Ioi (0 : ℝ)) => (hasDerivAt_symPhase hφ m dir r).hasDerivWithinAt)
    hmono.injOn g
  have hcoe (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal r ≤ ENNReal.ofReal ((2 * c)⁻¹) *
        ENNReal.ofReal |symPhaseDeriv φ m dir r| := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc2.le)]
    apply ENNReal.ofReal_le_ofReal
    calc
      r = (2 * c)⁻¹ * (2 * c * r) := by field_simp
      _ ≤ (2 * c)⁻¹ * |symPhaseDeriv φ m dir r| := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc2.le)
        exact (radial_deriv_lower hφ hell m hdir hr.le).trans (le_abs_self _)
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * c)⁻¹) *
        (ENNReal.ofReal |symPhaseDeriv φ m dir r| * g (symPhase φ m dir r)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [← mul_assoc]
      exact mul_le_mul_left (hcoe r hr) _
    _ = ENNReal.ofReal ((2 * c)⁻¹) *
        ∫⁻ s in symPhase φ m dir '' Ioi (0 : ℝ), g s := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hchange]
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self



def pairEquiv : (ℝ × ℝ) ≃ᵐ E2 :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma pairEquiv_measurePreserving : MeasurePreserving pairEquiv volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (volume_preserving_finTwoArrow ℝ).symm

lemma pairEquiv_apply (p : ℝ × ℝ) : pairEquiv p = WithLp.toLp 2 ![p.1, p.2] := rfl

lemma pairEquiv_continuous : Continuous pairEquiv := by
  change Continuous (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by fun_prop)

def direction (θ : ℝ) : E2 := pairEquiv (Real.cos θ, Real.sin θ)

lemma direction_norm (θ : ℝ) : ‖direction θ‖ = 1 := by
  have h : ‖direction θ‖ ^ 2 = 1 := by
    simp only [EuclideanSpace.real_norm_sq_eq, direction, pairEquiv_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (direction θ)]

lemma pairEquiv_polar (r θ : ℝ) : pairEquiv (polarCoord.symm (r, θ)) = r • direction θ := by
  ext i
  fin_cases i <;> simp [polarCoord_symm_apply, pairEquiv_apply, direction]

lemma polar_lintegral_le {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    (m : E2) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w : E2, g (φ (m + w) + φ (m - w)) ≤
      ENNReal.ofReal (Real.pi / c) * ∫⁻ s : ℝ, g s := by
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => g (φ (m + pairEquiv p) + φ (m - pairEquiv p))
  have hf : Measurable f := hg.comp <| Continuous.measurable <|
    (hφ.continuous.comp (continuous_const.add pairEquiv_continuous)).add
      (hφ.continuous.comp (continuous_const.sub pairEquiv_continuous))
  have hcomp : (∫⁻ w : E2, g (φ (m + w) + φ (m - w))) = ∫⁻ p, f p :=
    (pairEquiv_measurePreserving.lintegral_comp_emb pairEquiv.measurableEmbedding _).symm
  rw [hcomp, ← lintegral_comp_polarCoord_symm f]
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f (polarCoord.symm p)) := by
    apply measurable_fst.ennreal_ofReal.mul
    apply hf.comp
    change Measurable (fun p : ℝ × ℝ => (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    fun_prop
  rw [polarCoord_target]
  change (∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 * f (polarCoord.symm p)
    ∂(volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) ≤ _
  rw [← Measure.prod_restrict]
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  change (∫⁻ θ in Ioo (-Real.pi) Real.pi,
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f (polarCoord.symm (r, θ))) ≤ _
  calc
    _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal r * g (symPhase φ m (direction θ) r) := by
      simp only [f, pairEquiv_polar, symPhase]
    _ ≤ ∫⁻ _θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ((2 * c)⁻¹) * ∫⁻ s : ℝ, g s := by
      apply lintegral_mono
      intro θ
      exact radial_lintegral_le hφ hc hell m (direction_norm θ) g
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [mul_comm _ (ENNReal.ofReal _), ← mul_assoc,
        ← ENNReal.ofReal_mul (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi)]
      congr 1
      congr 1
      field_simp
      ring



lemma pair_graph_lintegral_le {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    {G : E2 × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ξ : E2, ∫⁻ η : E2, G (ξ + η, φ ξ + φ η) ≤
      ENNReal.ofReal (Real.pi / c) * ∫⁻ u : E2 × ℝ, G u := by
  have hswap : AEMeasurable
      (Function.uncurry (fun ξ η : E2 => G (ξ + η, φ ξ + φ η)))
      (volume.prod volume) := by
    apply Measurable.aemeasurable
    exact hG.comp ((continuous_fst.add continuous_snd).prodMk
      ((hφ.continuous.comp continuous_fst).add (hφ.continuous.comp continuous_snd))).measurable
  have hswap₂ : AEMeasurable
      (Function.uncurry (fun η m : E2 => G (m, φ (m - η) + φ η)))
      (volume.prod volume) := by
    apply Measurable.aemeasurable
    exact hG.comp (continuous_snd.prodMk
      ((hφ.continuous.comp (continuous_snd.sub continuous_fst)).add
        (hφ.continuous.comp continuous_fst))).measurable
  calc
    _ = ∫⁻ η : E2, ∫⁻ ξ : E2, G (ξ + η, φ ξ + φ η) := lintegral_lintegral_swap hswap
    _ = ∫⁻ η : E2, ∫⁻ m : E2, G (m, φ (m - η) + φ η) := by
      apply lintegral_congr
      intro η
      have hm : Measurable (fun m : E2 => G (m, φ (m - η) + φ η)) := by
        apply hG.comp
        exact (continuous_id.prodMk
          ((hφ.continuous.comp (continuous_id.sub continuous_const)).add
            continuous_const)).measurable
      have H := (measurePreserving_add_right (volume : Measure E2) η).lintegral_comp hm
      simpa only [add_sub_cancel_right] using H
    _ = ∫⁻ m : E2, ∫⁻ η : E2, G (m, φ (m - η) + φ η) := lintegral_lintegral_swap hswap₂
    _ = ∫⁻ m : E2, ∫⁻ w : E2,
        G (m, φ ((2 : ℝ)⁻¹ • m + w) + φ ((2 : ℝ)⁻¹ • m - w)) := by
      apply lintegral_congr
      intro m
      have hm : Measurable (fun η : E2 => G (m, φ (m - η) + φ η)) := by
        apply hG.comp
        exact (continuous_const.prodMk
            ((hφ.continuous.comp (continuous_const.sub continuous_id)).add hφ.continuous)).measurable
      have H := ((measurePreserving_add_left (volume : Measure E2) ((2 : ℝ)⁻¹ • m)).comp
        (Measure.measurePreserving_neg volume)).lintegral_comp hm
      symm
      convert H using 1
      congr 1
      ext w
      dsimp only [Function.comp_apply]
      have he : m - ((2 : ℝ)⁻¹ • m + -w) = (2 : ℝ)⁻¹ • m + w := by module
      simp only [he, sub_eq_add_neg]
    _ ≤ ∫⁻ m : E2, ENNReal.ofReal (Real.pi / c) * ∫⁻ s : ℝ, G (m, s) := by
      apply lintegral_mono
      intro m
      exact polar_lintegral_le hφ hc hell ((2 : ℝ)⁻¹ • m)
        (hG.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact (lintegral_prod G hG.aemeasurable).symm



def pairGraph (φ : E2 → ℝ) (z : E2 × E2) : E2 × ℝ :=
  (z.1 + z.2, φ z.1 + φ z.2)

lemma pairGraph_continuous {φ : E2 → ℝ} (hφ : Continuous φ) : Continuous (pairGraph φ) :=
  (continuous_fst.add continuous_snd).prodMk
    ((hφ.comp continuous_fst).add (hφ.comp continuous_snd))

lemma pairGraph_map_le {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v) :
    Measure.map (pairGraph φ) (volume.prod volume) ≤
      ENNReal.ofReal (Real.pi / c) • (volume : Measure (E2 × ℝ)) := by
  refine Measure.le_iff.mpr fun s hs => ?_
  let G : E2 × ℝ → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hG : Measurable G := measurable_const.indicator hs
  have H := pair_graph_lintegral_le hφ hc hell hG
  have heq : (∫⁻ ξ : E2, ∫⁻ η : E2, G (ξ + η, φ ξ + φ η)) =
      Measure.map (pairGraph φ) (volume.prod volume) s := by
    change (∫⁻ ξ : E2, ∫⁻ η : E2, G (pairGraph φ (ξ, η))) = _
    rw [← lintegral_prod (μ := volume) (ν := volume) (fun z : E2 × E2 => G (pairGraph φ z))
      (hG.comp (pairGraph_continuous hφ.continuous).measurable).aemeasurable]
    rw [← lintegral_map hG (pairGraph_continuous hφ.continuous).measurable]
    simp [G, hs]
  rw [heq] at H
  simpa only [G, lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ,
    one_mul, Measure.smul_apply, smul_eq_mul] using H

end DiagonalExtension.ConvexRadial

end

end OAI
