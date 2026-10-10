import OAI.Probability.GaussianReplacement.Density

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

lemma unitBallLaw_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    unitBallLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  have h0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have ht : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ ≤ ((volume : Measure E) (Metric.ball 0 1))⁻¹ * volume (Metric.closedBall z r) := by
      exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = _ := by
      rw [Measure.addHaar_closedBall _ _ hr.le, mul_comm _ (_ * _), mul_assoc,
        ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma unitBallLaw_local : HasLocalMassBound (unitBallLaw : Measure E)
    (Module.finrank ℝ E : ℝ) := by
  intro z _ r hr
  simpa only [Real.rpow_natCast] using unitBallLaw_closedBall z hr

lemma unitBallLaw_support : (unitBallLaw : Measure E).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  simp

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

lemma sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
  classical
  let L := (Submodule.span ℝ ({z} : Set E)).toAffineSubspace
  let : Nonempty L := ⟨⟨0, (Submodule.span ℝ ({z} : Set E)).zero_mem⟩⟩
  have hl : Module.finrank ℝ L.direction ≤ 1 := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    simpa using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hm : (Module.finrank ℝ L.direction : ℝ) + (Module.finrank ℝ E - 1 : ℕ) ≤
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (by omega : Module.finrank ℝ L.direction + (Module.finrank ℝ E - 1) ≤ Module.finrank ℝ E)
  have hsub : Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r}) ⊆
      {t | Metric.infDist t L ≤ r} := by
    rintro _ ⟨c, hc, _, ⟨s, hs, rfl⟩, rfl⟩
    have hz : c • z ∈ L := Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    exact (Metric.infDist_le_dist_of_mem hz).trans (by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc.1]
      exact (mul_le_mul_of_nonneg_left hs hc.1.le).trans (mul_le_of_le_one_left hr.le hc.2.le))
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L _ hm hr hr1).trans
  simp only [Real.rpow_natCast]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hl)
    (by positivity)

end SphereBounds



lemma uniformSphere_growth {d a : ℕ} (hd : 1 ≤ d) (ha : a ≤ d-1) :
    LocalGrowth (uniformSphere d) a ((3:ℝ)*4^d) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  intro z t ht
  have hf : Module.finrank ℝ (Vector d) = d := finrank_euclideanSpace_fin
  change sphereLaw {s : Sphere d | dist (s:Vector d) z ≤ t} ≤ _
  by_cases ht1 : t ≤ 1
  · have hh := sphereLaw_cap_raw z ht ht1 (by simpa only [hf] using hd)
    rw [hf] at hh
    apply hh.trans
    calc
      _ ≤ ENNReal.ofReal ((3:ℝ)*4^d) * ENNReal.ofReal (t^a) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one ht.le ht1 ha))
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  · calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply ENNReal.one_le_ofReal.mpr
        have h4 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n:=d)
        have ht' := one_le_pow₀ (le_of_not_ge ht1) (n:=a)
        nlinarith

lemma dominatedSphere_growth {d a : ℕ} (ν : Measure (Sphere d)) {H : ℝ}
    (hH : 0 ≤ H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hd : 1 ≤ d) (ha : a ≤ d-1) : LocalGrowth ν a (H * (3*4^d)) := by
  intro z t ht
  calc
    _ ≤ (ENNReal.ofReal H • uniformSphere d) _ := hν _
    _ = ENNReal.ofReal H * uniformSphere d _ := rfl
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal ((3*4^d)*t^a) :=
      mul_le_mul' le_rfl (uniformSphere_growth hd ha z t ht)
    _ = _ := by rw [← ENNReal.ofReal_mul hH]; congr 1; ring

lemma extended_eq_inverse_rnDeriv {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ y ∂labelLaw ρ G, extendedCubeDensity ρ G y = (volume.rnDeriv (labelLaw ρ G) y)⁻¹ := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume (labelLaw ρ G)] with y hy
  have ht := (hy.comp tendsto_cube_scale).inv
  have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => (volume (Metric.closedBall y (1/(j:ℝ))) /
        labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))))⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hjp : 0 < 1/(j:ℝ) := by positivity
    rw [cubeAverage_eq_ball_ratio ρ G y hjp,
      ENNReal.inv_div (Or.inl (measure_ne_top _ _))]
    exact Or.inr (by rw [Real.volume_pi_closedBall y hjp.le]; positivity)
  exact (ht.congr' he.symm).liminf_eq

lemma labelLaw_ac_of_finite_extended {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d)
    (hf : ∀ᵐ (s : Sphere d) ∂ρ, extendedCubeDensity ρ G (label G (s:Vector d)) < ∞) :
    labelLaw ρ G ≪ volume := by
  have hm : Measurable (fun y => extendedCubeDensity ρ G y) := by
    have hh := (measurable_extendedCubeDensity (k:=k) ρ).comp
      (show Measurable (fun y : Fin k → ℝ => (G,y)) from measurable_const.prodMk measurable_id)
    exact hh
  have hfy : ∀ᵐ y ∂labelLaw ρ G, extendedCubeDensity ρ G y < ∞ :=
    (ae_map_iff (by unfold label; fun_prop) (measurableSet_lt hm measurable_const)).mpr hf
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro p hp
  filter_upwards [extended_eq_inverse_rnDeriv ρ G, hfy,
    Measure.ae_rnDeriv_ne_zero_imp_of_ae (labelLaw ρ G) hp] with y he hy hpy
  apply hpy
  intro hz
  rw [he, hz, ENNReal.inv_zero] at hy
  exact (lt_irrefl _ hy)

lemma measurable_swapped_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Sphere d × Rows k d =>
      extendedCubeDensity ρ z.2 (label z.2 (z.1:Vector d))) := by
  have hh := (measurable_own_extended (k:=k) ρ).comp
    (show Measurable (Prod.swap : Sphere d × Rows k d → Rows k d × Sphere d) from measurable_swap)
  exact hh

lemma ae_labelLaw_ac_of_growth {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D) :
    ∀ᵐ G ∂gaussianRows (m+r) d, labelLaw ρ G ≪ volume := by
  have hf : ∀ᵐ G ∂gaussianRows (m+r) d, ∀ᵐ (s : Sphere d) ∂ρ,
      extendedCubeDensity ρ G (label G (s:Vector d)) < ∞ := by
    apply (Measure.ae_ae_comm ?_).mp
    · exact Filter.Eventually.of_forall (extended_ae_finite hdim ρ B D hB hD hBρ hDρ)
    · exact measurableSet_lt (measurable_swapped_extended (k:=m+r) ρ) measurable_const
  exact hf.mono (fun G hG => labelLaw_ac_of_finite_extended ρ G hG)



lemma volume_ae_cube_limit {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)),
      Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 (exactDensity ρ G y)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (labelLaw ρ G) volume,
    Measure.rnDeriv_ne_top (labelLaw ρ G) volume] with y hy hyt
  have ht := hy.comp tendsto_cube_scale
  have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))) /
        volume (Metric.closedBall y (1/(j:ℝ)))) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact cubeAverage_eq_ball_ratio ρ G y (by positivity)
  have htc := ht.congr' he.symm
  exact (exactDensity_eq_of_tendsto ρ G y htc hyt).symm ▸ htc



open InformationTheory



lemma entropy_exp_bound {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : klDiv P Q ≠ ∞) (f c : A → ℝ)
    (hf : Measurable f) (hc : Measurable c) (hf0 : ∀ x, 0 ≤ f x)
    (hci : Integrable c P)
    (hExp : ∫⁻ x, ENNReal.ofReal (Real.exp (f x-c x)) ∂Q ≤ 1) :
    Integrable f P ∧ ∫ x, f x ∂P ≤ (klDiv P Q).toReal + ∫ x, c x ∂P := by
  obtain ⟨hPQ, hllr⟩ := klDiv_ne_top_iff.mp hKL
  let v : A → ℝ := fun x => Real.exp (f x-c x-llr P Q x)
  have hvm : Measurable v := (hf.sub hc |>.sub (measurable_llr P Q)).exp
  have hv0 (x : A) : 0 ≤ v x := (Real.exp_pos _).le
  have hvbound : ∫⁻ x, ENNReal.ofReal (v x) ∂P ≤ 1 := by
    rw [← lintegral_rnDeriv_mul hPQ hvm.ennreal_ofReal.aemeasurable]
    apply le_trans (lintegral_mono_ae ?_) hExp
    filter_upwards [Measure.rnDeriv_ne_top P Q] with x hxt
    by_cases hx0 : P.rnDeriv Q x = 0
    · simp [hx0]
    · have hxr : 0 < (P.rnDeriv Q x).toReal := ENNReal.toReal_pos hx0 hxt
      dsimp only [v]
      rw [Real.exp_sub, llr_def, Real.exp_log hxr, ENNReal.ofReal_div_of_pos hxr,
        ENNReal.ofReal_toReal hxt, div_eq_mul_inv, ← mul_assoc,
        mul_comm (P.rnDeriv Q x), mul_assoc, ENNReal.mul_inv_cancel hx0 hxt, mul_one]
  have hvi : Integrable v P :=
    (lintegral_ofReal_ne_top_iff_integrable hvm.aestronglyMeasurable
      (Filter.Eventually.of_forall hv0)).mp (ne_of_lt (hvbound.trans_lt (by simp)))
  have hvint : ∫ x, v x ∂P ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hvi (Filter.Eventually.of_forall hv0)] at hvbound
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (by simpa using hvbound)
  have hle : ∀ x, f x ≤ llr P Q x + c x + v x - 1 := by
    intro x
    have he := Real.add_one_le_exp (f x-c x-llr P Q x)
    dsimp only [v]
    linarith
  have hup : Integrable (fun x => llr P Q x + c x + v x - 1) P :=
    ((hllr.add hci).add hvi).sub (integrable_const 1)
  have hfi : Integrable f P := integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hle) (integrable_zero _ _ _) hup
  refine ⟨hfi, ?_⟩
  have hb := integral_mono hfi hup hle
  have hi : (∫ x, llr P Q x + c x + v x - 1 ∂P) =
      (∫ x, llr P Q x ∂P) + (∫ x, c x ∂P) + (∫ x, v x ∂P) - 1 := by
    rw [integral_sub (f:=fun x => llr P Q x+c x+v x) (g:=fun _ => 1)
      ((hllr.add hci).add hvi) (integrable_const 1)]
    rw [integral_add (f:=fun x => llr P Q x+c x) (g:=v) (hllr.add hci) hvi]
    rw [integral_add hllr hci, integral_const]
    simp
  rw [hi] at hb
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  linarith


lemma lintegral_one_add_pow_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ≥0∞)
    (hF : Measurable F) {q : ℕ} (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hC : ∫⁻ x, (F x)^q ∂μ ≤ C^q) :
    ∫⁻ x, (1+F x)^q ∂μ ≤ (1+C)^q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hh := ENNReal.lintegral_Lp_add_le (μ:=μ) (f:=fun _ : A => (1:ℝ≥0∞)) (g:=F)
    measurable_const.aemeasurable hF.aemeasurable (show (1:ℝ) ≤ q by exact_mod_cast hq)
  simp only [Pi.add_apply, ENNReal.rpow_natCast, one_pow,
    lintegral_const, measure_univ, mul_one, ENNReal.one_rpow] at hh
  have hFroot : (∫⁻ x, (F x)^q ∂μ) ^ (1/(q:ℝ)) ≤ C := by
    apply (ENNReal.rpow_le_rpow hC (by positivity)).trans_eq
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hroot := hh.trans (add_le_add_right hFroot 1)
  have hpow := ENNReal.rpow_le_rpow hroot hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at hpow
  exact hpow




end CurrentProjection

end

end OAI
