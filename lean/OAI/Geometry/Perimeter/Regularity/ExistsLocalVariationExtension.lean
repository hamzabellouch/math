import OAI.Geometry.Perimeter.Regularity.SmoothLayerSumBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_local_variation_extension {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    ∃ F : Lp (Euc n) 2 ((perimeterMeasure E).restrict U) →ₗ[ℝ] ℝ,
      (∀ u : smoothVariationDomain U ((perimeterMeasure E).restrict U),
        F (u : Lp (Euc n) 2 ((perimeterMeasure E).restrict U)) = localVariationFunctional E U hU hP u) ∧
      ∀ u, |F u| ≤ ∫ x in U, ‖u x‖ ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict U
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  let p : Lp (Euc n) 2 μ →ₗ.[ℝ] ℝ :=
    ⟨smoothVariationDomain U μ, localVariationFunctional E U hU hP⟩
  let N : Lp (Euc n) 2 μ → ℝ := fun u ↦ ∫ x, ‖u x‖ ∂μ
  have hi : ∀ u : Lp (Euc n) 2 μ, Integrable (fun x ↦ ‖u x‖) μ :=
    fun u ↦ (memLp_one_iff_integrable.mp ((Lp.memLp u).mono_exponent (by norm_num))).norm
  have hhom : ∀ c : ℝ, 0 < c → ∀ u, N (c • u) = c * N u := by
    intro c hc u
    dsimp [N]
    calc
      _ = ∫ x, c * ‖u x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c u] with x hx
        rw [hx, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc.le]
      _ = _ := integral_const_mul _ _
  have hadd : ∀ u v, N (u + v) ≤ N u + N v := by
    intro u v
    dsimp [N]
    rw [← integral_add (hi u) (hi v)]
    apply integral_mono_ae (hi (u + v)) ((hi u).add (hi v))
    filter_upwards [Lp.coeFn_add u v] with x hx
    rw [hx, Pi.add_apply]
    exact norm_add_le _ _
  obtain ⟨F, hF, hFn⟩ := exists_extension_of_le_sublinear p N hhom hadd
    (fun u ↦ (le_abs_self _).trans (localVariationFunctional_le E U hU hP u))
  refine ⟨F, hF, fun u ↦ abs_le.mpr ⟨?_, hFn u⟩⟩
  have hh := hFn (-u)
  have he : N (-u) = N u := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg u] with x hx
    rw [hx, Pi.neg_apply, norm_neg]
  rw [map_neg, he] at hh
  linarith

theorem local_l2_integral_norm_le {n : ℕ} (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (u : Lp (Euc n) 2 μ) :
    (∫ x, ‖u x‖ ∂μ) ≤ (μ univ ^ (1 / 2 : ℝ)).toReal * ‖u‖ := by
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := (u : Euc n → Euc n))
    (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable u)
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hh
  have ht : eLpNorm (u : Euc n → Euc n) 2 μ * μ univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))
  have hr := ENNReal.toReal_mono ht hh
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable u), ENNReal.toReal_mul,
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u), ← Lp.norm_def] at hr
  simpa [mul_comm] using hr

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem l2_polar_norm_le_one {n : ℕ} (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (G : Lp (Euc n) 2 μ)
    (hG : ∀ u : Lp (Euc n) 2 μ,
      inner ℝ G u ≤ ∫ x, ‖u x‖ ∂μ) :
    ∀ᵐ x ∂μ, ‖G x‖ ≤ 1 := by
  let s := {x | 1 < ‖G x‖}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (Lp.stronglyMeasurable G).measurable.norm
  have hu : MemLp (s.indicator (G : Euc n → Euc n)) 2 μ := (Lp.memLp G).indicator hs
  let u : Lp (Euc n) 2 μ := hu.toLp _
  have he : (u : Euc n → Euc n) =ᵐ[μ] s.indicator (G : Euc n → Euc n) := hu.coeFn_toLp
  have hsq : Integrable (fun x ↦ ‖G x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.integrable_inner (𝕜 := ℝ) G G)
  have hn : Integrable (fun x ↦ ‖G x‖) μ :=
    (memLp_one_iff_integrable.mp ((Lp.memLp G).mono_exponent (by norm_num))).norm
  let a : Euc n → ℝ := s.indicator (fun x ↦ ‖G x‖ ^ 2)
  let b : Euc n → ℝ := s.indicator (fun x ↦ ‖G x‖)
  have hai : Integrable a μ := hsq.indicator hs
  have hbi : Integrable b μ := hn.indicator hs
  have hea : inner ℝ G u = ∫ x, a x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
    by_cases hsx : x ∈ s
    · simp [a, hsx]
    · simp [a, hsx]
  have heb : (∫ x, ‖u x‖ ∂μ) = ∫ x, b x ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
    by_cases hsx : x ∈ s <;> simp [b, hsx]
  have hab := hG u
  rw [hea, heb] at hab
  have hnonneg : ∀ x, 0 ≤ a x - b x := by
    intro x
    by_cases hx : x ∈ s
    · have hh : 1 < ‖G x‖ := hx
      simp only [a, b, indicator_of_mem hx]
      nlinarith
    · simp [a, b, hx]
  have hz : (∫ x, a x - b x ∂μ) = 0 := by
    apply le_antisymm
    · rw [integral_sub hai hbi]; linarith
    · exact integral_nonneg hnonneg
  have hae : ∀ᵐ x ∂μ, a x - b x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hnonneg) (hai.sub hbi)).mp hz
  filter_upwards [hae] with x hx
  by_contra h
  have hlt : 1 < ‖G x‖ := lt_of_not_ge h
  have hsx : x ∈ s := hlt
  simp only [a, b, indicator_of_mem hsx] at hx
  nlinarith

theorem exists_local_variation_polar {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    ∃ G : Euc n → Euc n,
      StronglyMeasurable G ∧
      MemLp G 2 ((perimeterMeasure E).restrict U) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U, ‖G x‖ ≤ 1) ∧
      ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V ⊆ U →
        (∫ x in E, divergence V x) = ∫ x in U, inner ℝ (G x) (V x) ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict U
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  obtain ⟨F, hF, hFb⟩ := exists_local_variation_extension E U hU hP
  let C : ℝ := (μ univ ^ (1 / 2 : ℝ)).toReal
  have hFc : ∀ u, ‖F u‖ ≤ C * ‖u‖ := fun u ↦
    (hFb u).trans (local_l2_integral_norm_le μ u)
  let Fc : Lp (Euc n) 2 μ →L[ℝ] ℝ := F.mkContinuous C hFc
  let G : Lp (Euc n) 2 μ := (InnerProductSpace.toDual ℝ (Lp (Euc n) 2 μ)).symm Fc
  have hrep : ∀ u, inner ℝ G u = F u := fun u ↦ InnerProductSpace.toDual_symm_apply
  have hnorm : ∀ᵐ x ∂μ, ‖G x‖ ≤ 1 := l2_polar_norm_le_one μ G
    (fun u ↦ by rw [hrep]; exact (le_abs_self _).trans (hFb u))
  refine ⟨G, Lp.stronglyMeasurable G, Lp.memLp G, hnorm, ?_⟩
  intro V hV hc hs
  obtain ⟨B, hB⟩ := (hc.isCompact_range hV.continuous).isBounded.exists_norm_le
  have hVm : MemLp V 2 μ := MemLp.of_bound hV.continuous.aestronglyMeasurable B
    (ae_of_all _ (fun x ↦ hB _ (mem_range_self x)))
  let u : Lp (Euc n) 2 μ := hVm.toLp V
  have heu : (u : Euc n → Euc n) =ᵐ[μ] V := hVm.coeFn_toLp
  let v : smoothVariationDomain U μ := ⟨u, V, hV, hc, hs, heu⟩
  obtain ⟨hR, hcR, hsR, heR⟩ := smoothVariationRepresentative_spec v
  have hval : localVariationFunctional E U hU hP v = ∫ x in E, divergence V x :=
    integral_divergence_eq_of_variation_ae E U hU hP hR hcR hsR hV hc hs (heR.symm.trans heu)
  calc
    (∫ x in E, divergence V x) = F u := hval.symm.trans (hF v).symm
    _ = inner ℝ G u := (hrep u).symm
    _ = ∫ x, inner ℝ (G x) (V x) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [heu] with x hx
      rw [hx]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_local_unit_variation_polar {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    ∃ G : Euc n → Euc n,
      StronglyMeasurable G ∧
      MemLp G 2 ((perimeterMeasure E).restrict U) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U, ‖G x‖ = 1) ∧
      ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V ⊆ U →
        (∫ x in E, divergence V x) = ∫ x in U, inner ℝ (G x) (V x) ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict U
  have hμu : μ univ = perimeter E U := by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]
  let : IsFiniteMeasure μ := ⟨by rw [hμu]; exact hP.lt_top⟩
  obtain ⟨G, hG, hGp, hGn, hrep⟩ := exists_local_variation_polar E U hU hP
  have hGi : Integrable (fun x ↦ ‖G x‖) μ :=
    (memLp_one_iff_integrable.mp (hGp.mono_exponent (by norm_num))).norm
  have hvar : perimeter E U ≤ ENNReal.ofReal (∫ x, ‖G x‖ ∂μ) := by
    rw [perimeter_eq_iSup_tests]
    apply iSup_le
    intro V
    apply iSup_le
    intro hV
    apply ENNReal.ofReal_le_ofReal
    rw [hrep V hV.1 hV.2.1 hV.2.2.1]
    have hb : ∀ᵐ x ∂μ, ‖inner ℝ (G x) (V x)‖ ≤ 1 := by
      filter_upwards [hGn] with x hx
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hx).trans (hV.2.2.2 x))
    have hi : Integrable (fun x ↦ inner ℝ (G x) (V x)) μ :=
      Integrable.of_bound (hG.aestronglyMeasurable.inner hV.1.continuous.aestronglyMeasurable) 1 hb
    apply integral_mono hi hGi
    intro x
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hV.2.2.2 x) (norm_nonneg _)).trans_eq (mul_one _))
  have hlow : μ.real univ ≤ ∫ x, ‖G x‖ ∂μ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ norm_nonneg _))] at hh
    simpa only [measureReal_def, hμu] using hh
  have hnneg : ∀ᵐ x ∂μ, 0 ≤ (1 : ℝ) - ‖G x‖ := hGn.mono fun x hx ↦ sub_nonneg.mpr hx
  have hz : (∫ x, (1 : ℝ) - ‖G x‖ ∂μ) = 0 := by
    apply le_antisymm
    · rw [integral_sub (integrable_const 1) hGi, integral_const]
      simp only [smul_eq_mul, mul_one]
      linarith
    · exact integral_nonneg_of_ae hnneg
  have he : ∀ᵐ x ∂μ, (1 : ℝ) - ‖G x‖ = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnneg ((integrable_const 1).sub hGi)).mp hz
  exact ⟨G, hG, hGp, he.mono (fun x hx ↦ by linarith), hrep⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem smooth_translation_lintegral_le {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ 1 u) (a : Euc n) :
    (∫⁻ x, ‖u (x + a) - u x‖ₑ) ≤ ‖a‖ₑ * ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by
  have hfd := hu.continuous_fderiv one_ne_zero
  have hpoint (x : Euc n) :
      ‖u (x + a) - u x‖ₑ ≤
        ∫⁻ t in Ioc (0 : ℝ) 1, ‖a‖ₑ * ‖fderiv ℝ u (x + t • a)‖ₑ := by
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ u (x + s • a))
        (fderiv ℝ u (x + t • a) a) t := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hu.differentiable one_ne_zero (x + t • a)).hasFDerivAt.comp_hasDerivAt t
          (HasDerivAt.const_add x ((hasDerivAt_id t).smul_const a))
    have hi : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ u (x + t • a) a) volume 0 1 :=
      ((hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).intervalIntegrable _ _
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
    simp only [one_smul, zero_smul, add_zero] at he
    rw [← he, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono
    intro t
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((ContinuousLinearMap.le_opNorm _ _).trans_eq (mul_comm _ _))
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖a‖ₑ * ‖fderiv ℝ u (p.1 + p.2 • a)‖ₑ) :=
    measurable_const.mul ((hfd.comp (continuous_fst.add
      (continuous_snd.smul continuous_const))).enorm.measurable)
  calc
    (∫⁻ x, ‖u (x + a) - u x‖ₑ) ≤
        ∫⁻ x, ∫⁻ t in Ioc (0 : ℝ) 1, ‖a‖ₑ * ‖fderiv ℝ u (x + t • a)‖ₑ :=
      lintegral_mono hpoint
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x, ‖a‖ₑ * ‖fderiv ℝ u (x + t • a)‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ‖a‖ₑ * ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by
      apply lintegral_congr
      intro t
      have hmt : Measurable (fun x : Euc n ↦ ‖fderiv ℝ u (x + t • a)‖ₑ) :=
        (hfd.comp (continuous_id.add continuous_const)).enorm.measurable
      rw [lintegral_const_mul _ hmt,
        lintegral_add_right_eq_self (fun x : Euc n ↦ ‖fderiv ℝ u x‖ₑ) (t • a)]
    _ = ‖a‖ₑ * ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by simp

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary
open scoped Convolution

theorem indicator_translation_lintegral_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hb : Bornology.IsBounded E) (hP : perimeter E univ ≠ ⊤)
    (a : Euc n) :
    (∫⁻ x, ‖E.indicator (fun _ ↦ (1 : ℝ)) (x + a) -
      E.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) ≤ ‖a‖ₑ * perimeter E univ := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let u : ℕ → Euc n → ℝ := c1Mollify χ
  obtain ⟨hχ, hcχ⟩ := indicator_one_integrable_compact hE hb
  have hu : ∀ j, ContDiff ℝ ∞ (u j) := fun j ↦
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hχ.locallyIntegrable
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hχ.locallyIntegrable
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  have hlimadd : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j (x + a)) atTop (𝓝 (χ (x + a))) :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hlim
  have hlimnorm : ∀ᵐ x ∂volume,
      Tendsto (fun j ↦ ‖u j (x + a) - u j x‖ₑ) atTop (𝓝 (‖χ (x + a) - χ x‖ₑ)) := by
    filter_upwards [hlimadd, hlim] with x hx hy
    exact (hx.sub hy).enorm
  calc
    (∫⁻ x, ‖χ (x + a) - χ x‖ₑ) =
        ∫⁻ x, liminf (fun j ↦ ‖u j (x + a) - u j x‖ₑ) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hlimnorm] with x hx using hx.liminf_eq.symm
    _ ≤ liminf (fun j ↦ ∫⁻ x, ‖u j (x + a) - u j x‖ₑ) atTop :=
      lintegral_liminf_le' (fun j ↦ (((hu j).continuous.comp
        (continuous_id.add continuous_const)).sub (hu j).continuous).enorm.measurable.aemeasurable)
    _ ≤ ‖a‖ₑ * perimeter E univ := by
      have hb' : ∀ j, (∫⁻ x, ‖u j (x + a) - u j x‖ₑ) ≤ ‖a‖ₑ * perimeter E univ := by
        intro j
        apply (smooth_translation_lintegral_le ((hu j).of_le (by simp)) a).trans
        gcongr
        exact c1Mollify_indicator_gradient_le_perimeter hE hb hP j
      exact liminf_le_of_frequently_le (Eventually.of_forall hb').frequently

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
open scoped Convolution

theorem c1Mollify_indicator_lintegral_error_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hb : Bornology.IsBounded E) (hP : perimeter E univ ≠ ⊤)
    (j : ℕ) :
    (∫⁻ x, ‖c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x -
      E.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) ≤
      ENNReal.ofReal (c1Mollifier (n := n) j).rOut * perimeter E univ := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  have hmχ : Measurable χ := measurable_const.indicator hE
  have hbχ : ∀ x, ‖χ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hkc : Continuous k := (c1Mollifier j).continuous_normed
  have hk : Integrable k volume := hkc.integrable_of_hasCompactSupport
    (c1Mollifier j).hasCompactSupport_normed
  have hk1 : ∫ x, k x = 1 := (c1Mollifier j).integral_normed
  have hp (x : Euc n) : ‖c1Mollify χ j x - χ x‖ₑ ≤
      ∫⁻ y, ‖k y‖ₑ * ‖χ (x - y) - χ x‖ₑ := by
    have hi : Integrable (fun y ↦ k y * χ (x - y)) volume := by
      apply hk.norm.mono'
      · exact (hkc.measurable.mul (hmχ.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      · apply ae_of_all
        intro y
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hbχ (x - y)) (norm_nonneg _)).trans_eq (mul_one _)
    have he : c1Mollify χ j x - χ x = ∫ y, k y * (χ (x - y) - χ x) := by
      simp only [c1Mollify, convolution_def, lsmul_apply, smul_eq_mul]
      simp_rw [mul_sub]
      rw [integral_sub hi (hk.mul_const _), integral_mul_const, hk1, one_mul]
    rw [he]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    apply lintegral_congr
    intro y
    exact enorm_mul _ _
  have hm : Measurable (fun p : Euc n × Euc n ↦
      ‖k p.2‖ₑ * ‖χ (p.1 - p.2) - χ p.1‖ₑ) :=
    (hkc.measurable.comp measurable_snd).enorm.mul
      ((hmχ.comp (measurable_fst.sub measurable_snd)).sub
        (hmχ.comp measurable_fst)).enorm
  calc
    (∫⁻ x, ‖c1Mollify χ j x - χ x‖ₑ) ≤
        ∫⁻ x, ∫⁻ y, ‖k y‖ₑ * ‖χ (x - y) - χ x‖ₑ := lintegral_mono hp
    _ = ∫⁻ y, ∫⁻ x, ‖k y‖ₑ * ‖χ (x - y) - χ x‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖χ (x - y) - χ x‖ₑ := by
      apply lintegral_congr
      intro y
      apply lintegral_const_mul
      exact ((hmχ.comp (measurable_id.sub measurable_const)).sub hmχ).enorm
    _ ≤ ∫⁻ y, ‖k y‖ₑ * (‖y‖ₑ * perimeter E univ) := by
      apply lintegral_mono
      intro y
      have hy : (∫⁻ x, ‖χ (x - y) - χ x‖ₑ) ≤ ‖y‖ₑ * perimeter E univ := by
        simpa only [sub_eq_add_neg, enorm_neg] using indicator_translation_lintegral_le hE hb hP (-y)
      exact mul_le_mul_right hy _
    _ ≤ ∫⁻ y, ‖k y‖ₑ * (ENNReal.ofReal (c1Mollifier (n := n) j).rOut * perimeter E univ) := by
      apply lintegral_mono
      intro y
      by_cases hy : k y = 0
      · simp only [hy, enorm_zero, zero_mul, le_refl]
      · have hys : y ∈ Function.support k := hy
        rw [(c1Mollifier j).support_normed_eq] at hys
        have hyb : ‖y‖ₑ ≤ ENNReal.ofReal (c1Mollifier (n := n) j).rOut := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by
            have hylt : ‖y‖ < (c1Mollifier (n := n) j).rOut := by
              simpa only [Metric.mem_ball, dist_zero_right] using hys
            exact hylt.le)
        exact mul_le_mul_right (mul_le_mul_left hyb _) _
    _ = ENNReal.ofReal (c1Mollifier (n := n) j).rOut * perimeter E univ := by
      rw [lintegral_mul_const _ hkc.measurable.enorm]
      have hki : (∫⁻ y, ‖k y‖ₑ) = 1 := by
        have heq : ∀ y, ‖k y‖ₑ = ENNReal.ofReal (k y) := by
          intro y
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ((c1Mollifier j).nonneg_normed y)]
        simp_rw [heq]
        rw [← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ (c1Mollifier j).nonneg_normed), hk1]
        norm_num
      rw [hki, one_mul]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
open scoped Convolution NNReal

theorem c1Mollify_indicator_mem_Icc {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (j : ℕ) (x : Euc n) :
    c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x ∈ Icc (0 : ℝ) 1 := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  have hk0 : ∀ y, 0 ≤ k y := (c1Mollifier j).nonneg_normed
  have hk : Integrable k volume := (c1Mollifier j).continuous_normed.integrable_of_hasCompactSupport
    (c1Mollifier j).hasCompactSupport_normed
  have hχb : ∀ y, χ y ∈ Icc (0 : ℝ) 1 := by
    intro y
    by_cases hy : y ∈ E <;> simp [χ, hy]
  change (∫ y, k y * χ (x - y)) ∈ Icc (0 : ℝ) 1
  refine ⟨integral_nonneg (fun y ↦ mul_nonneg (hk0 y) (hχb _).1), ?_⟩
  calc
    (∫ y, k y * χ (x - y)) ≤ ∫ y, k y := by
      have hnonneg : ∀ᵐ y ∂volume, 0 ≤ k y * χ (x - y) :=
        ae_of_all _ fun y ↦ mul_nonneg (hk0 y) (hχb _).1
      have hbound : ∀ᵐ y ∂volume, k y * χ (x - y) ≤ k y := by
        apply ae_of_all
        intro y
        exact (mul_le_mul_of_nonneg_left (hχb _).2 (hk0 y)).trans_eq (mul_one _)
      have hm : AEStronglyMeasurable (fun y ↦ k y * χ (x - y)) volume :=
        ((c1Mollifier j).continuous_normed.measurable.mul
          ((measurable_const.indicator hE).comp
            (measurable_const.sub measurable_id))).aestronglyMeasurable
      exact integral_mono_ae (hk.mono_nonneg hm hnonneg hbound) hk hbound
    _ = 1 := (c1Mollifier j).integral_normed

theorem c1Mollify_indicator_uniform_lipschitz {n : ℕ} (K : Set (Euc n))
    (hK : Bornology.IsBounded K) (j : ℕ) :
    ∃ L : ℝ≥0, ∀ E : Set (Euc n), MeasurableSet E → E ⊆ K →
      LipschitzWith L (c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j) := by
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (n := ∞) (f := k) (c1Mollifier j).hasCompactSupport_normed
    (c1Mollifier j).contDiff_normed (by simp)
  refine ⟨C * (volume K).toNNReal, ?_⟩
  intro E hE hEK
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  obtain ⟨hiχ, hcχ⟩ := indicator_one_integrable_compact hE (hK.subset hEK)
  have hχ0 : ∀ z, 0 ≤ χ z := fun z ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) z
  have hχ1 : ∫ z, χ z ≤ volume.real K := by
    rw [show χ = E.indicator (fun _ ↦ (1 : ℝ)) from rfl, integral_indicator hE]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    exact ENNReal.toReal_mono hK.measure_lt_top.ne (measure_mono hEK)
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have hf : c1Mollify χ j = χ ⋆[lsmul ℝ ℝ, volume] k := by
    change k ⋆[lsmul ℝ ℝ, volume] χ = _
    rw [← convolution_flip, hflip]
  have hib (x : Euc n) : Integrable (fun z ↦ χ z * k (x - z)) volume := by
    obtain ⟨B, hB⟩ := ((c1Mollifier (n := n) j).hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous
      (c1Mollifier j).continuous_normed
    apply (hiχ.norm.mul_const B).mono'
    · exact ((measurable_const.indicator hE).mul
        ((c1Mollifier j).continuous_normed.measurable.comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
    · apply ae_of_all
      intro z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, hf]
  change ‖(∫ z, χ z * k (x - z)) - ∫ z, χ z * k (y - z)‖ ≤ _
  rw [← integral_sub (hib x) (hib y)]
  calc
    ‖∫ z, χ z * k (x - z) - χ z * k (y - z)‖ ≤
        ∫ z, ‖χ z * k (x - z) - χ z * k (y - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, χ z * ((C : ℝ) * dist x y) := by
      apply integral_mono ((hib x).sub (hib y)).norm (hiχ.mul_const _)
      intro z
      change ‖χ z * k (x - z) - χ z * k (y - z)‖ ≤
        χ z * ((C : ℝ) * dist x y)
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]
      apply mul_le_mul_of_nonneg_left _ (hχ0 z)
      simpa only [← dist_eq_norm, dist_sub_right] using hC.dist_le_mul (x - z) (y - z)
    _ = (∫ z, χ z) * ((C : ℝ) * dist x y) := integral_mul_const _ _
    _ ≤ volume.real K * ((C : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_right hχ1 (mul_nonneg C.coe_nonneg dist_nonneg)
    _ = ((C * (volume K).toNNReal : ℝ≥0) : ℝ) * dist x y := by
      change volume.real K * ((C : ℝ) * dist x y) =
        ((C : ℝ) * volume.real K) * dist x y
      ring

end RPISingularHarnack

end

end OAI
