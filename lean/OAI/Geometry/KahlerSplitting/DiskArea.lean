import OAI.Geometry.KahlerSplitting.MovingStokes

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set MeasureTheory

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Interval

lemma finTwo_box_integral_eq_prod (F : (Fin 2 → ℝ) → ℝ) (a b : Fin 2 → ℝ) :
    (∫ y in Icc a b, F y) =
      ∫ p in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1), F ![p.1,p.2] := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have hp : e ⁻¹' (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) = Icc a b := by
    ext y
    simp only [e, MeasurableEquiv.finTwoArrow_apply, mem_preimage, mem_prod,
      mem_Icc, Pi.le_def, Fin.forall_fin_two]
    tauto
  have hh := ((volume_preserving_finTwoArrow ℝ).restrict_preimage_emb
    e.measurableEmbedding (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1))).integral_comp'
      (fun p ↦ F (e.symm p))
  rw [hp] at hh
  have he (p : ℝ × ℝ) : e.symm p = ![p.1,p.2] := by
    ext i
    fin_cases i <;> rfl
  change (∫ x in Icc a b, F (e.symm (e x))) =
    ∫ p in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1), F (e.symm p) at hh
  simp only [MeasurableEquiv.symm_apply_apply] at hh
  simpa only [he] using hh

theorem normalized_polar_integral_eq_disk {f : ℂ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (closedBall 0 R)) :
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      y 0 * R^2 * f (((R * y 0 : ℝ) : ℂ) * Complex.exp ((y 1 : ℂ) * Complex.I))) =
    ∫ z in ball (0 : ℂ) R, f z := by
  let G : ℝ × ℝ → ℝ := fun p ↦ p.1 * R^2 *
    f (((R * p.1 : ℝ) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
  have hc : ContinuousOn G (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) := by
    apply (continuousOn_fst.mul continuousOn_const).mul (hf.comp _ _)
    · fun_prop
    · intro p hp
      simp only [mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [Real.norm_of_nonneg hR, Real.norm_of_nonneg hp.1.1]
      nlinarith [hp.1.2]
  have hi : IntegrableOn G (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) :=
    hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [finTwo_box_integral_eq_prod]
  change (∫ p in Icc 0 1 ×ˢ Icc 0 (2 * Real.pi), G p) = _
  rw [Measure.volume_eq_prod, setIntegral_prod G
    (by simpa only [← Measure.volume_eq_prod] using hi)]
  have hinner (r : ℝ) : (∫ θ in Icc 0 (2 * Real.pi), G (r,θ)) =
      r * R^2 * (2 * Real.pi * Real.circleAverage f 0 (R*r)) := by
    change (∫ θ in Icc 0 (2 * Real.pi), r * R^2 *
      f (((R*r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = _
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (show 0 ≤ 2 * Real.pi by positivity)]
    congr 1
    rw [Real.circleAverage_def]
    simp only [smul_eq_mul, mul_inv_cancel_left₀ (by positivity : 2 * Real.pi ≠ 0)]
    simp only [circleMap, zero_add]
  simp_rw [hinner]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    disk_integral_eq_polar hR hf]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := 1) (fun t ↦ t * Real.circleAverage f 0 t) R
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  calc
    _ = 2 * Real.pi * (R * ∫ r in (0:ℝ)..1, (R*r) * Real.circleAverage f 0 (R*r)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = _ := by rw [hs]

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Manifold
variable {n : ℕ} {X : ComplexManifold n}

def sliceDensity (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (s z : ℂ) : ℝ :=
  pullbackMetric g f (s,z) (0,1) (0,1)

theorem sliceDensity_nonneg (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (s z : ℂ) :
    0 ≤ sliceDensity g f s z := g.nonnegative _ _

theorem curveSpeed_slice_sq (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {s z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f (s,z)) :
    curveSpeed g (fun w ↦ f (s,w)) z ^ 2 = sliceDensity g f s z := by
  have hp : HasFDerivAt (fun w : ℂ ↦ (s,w))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) z := hasFDerivAt_prodMk_right s z
  have hc : (fun w ↦ f (s,w)) = f ∘ (fun w : ℂ ↦ (s,w)) := rfl
  unfold curveSpeed
  rw [hc, mfderiv_comp z hf hp.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv,
    hp.fderiv]
  change metricNorm g (f (s,z))
    (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (s,z) (0,1)) ^ 2 = _
  exact Real.sq_sqrt (g.nonnegative _ _)

theorem sliceDensity_continuousOn (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {V : Set ℂ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hV : MapsTo (fun z ↦ (s,z)) V U) :
    ContinuousOn (sliceDensity g f s) V := by
  exact (((pullbackMetric_smooth g hU hf).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hV).clm_apply
      continuousOn_const).clm_apply continuousOn_const

theorem curveArea_slice_eq_ofReal_integral (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z ↦ (s,z)) (closedBall 0 R) U) :
    curveArea g (fun z ↦ f (s,z)) (ball 0 R) =
      ENNReal.ofReal (∫ z in ball (0 : ℂ) R, sliceDensity g f s z) := by
  have hi : IntegrableOn (sliceDensity g f s) (closedBall 0 R) :=
    (sliceDensity_continuousOn g hU hf hmap).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  have hD : ∀ z ∈ ball (0 : ℂ) R,
      curveSpeed g (fun t ↦ f (s,t)) z ^ 2 = sliceDensity g f s z := by
    intro z hz
    exact curveSpeed_slice_sq g (hf.mdifferentiableAt
      (hU.mem_nhds (hmap (ball_subset_closedBall hz))))
  unfold curveArea
  rw [setLIntegral_congr_fun measurableSet_ball (fun z hz ↦ congrArg ENNReal.ofReal (hD z hz))]
  exact (ofReal_integral_eq_lintegral_ofReal (hi.mono_set ball_subset_closedBall)
    (Filter.Eventually.of_forall (sliceDensity_nonneg g f s))).symm

theorem movingKahlerForm_zero_density (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 0 x =
      x 1 * R (x 0)^2 * sliceDensity g f (x 0)
        (((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingKahlerForm_zero g f hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change x 1 * R (x 0)^2 * g.metric _
      (D (0,Complex.exp ((x 2 : ℂ) * Complex.I)))
      (D (0,Complex.exp ((x 2 : ℂ) * Complex.I))) =
    x 1 * R (x 0)^2 * g.metric _ (D (0,1)) (D (0,1))
  have hv : ((0,Complex.exp ((x 2 : ℂ) * Complex.I)) : ℂ × ℂ) =
      Complex.exp ((x 2 : ℂ) * Complex.I) • (0,1) := by simp
  rw [hv, map_smul, g.quadratic_complex_smul, Complex.norm_exp_ofReal_mul_I]
  simp

theorem moving_disk_face_eq_areaIntegral (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ} {s : ℝ}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z : ℂ ↦ ((s : ℂ),z)) (closedBall 0 (R s)) U)
    (hR : DifferentiableAt ℝ R s) (hpos : 0 ≤ R s) :
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y)) =
    ∫ z in ball (0 : ℂ) (R s), sliceDensity g f s z := by
  have he (y : Fin 2 → ℝ) :
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y) =
      y 0 * (R s)^2 * sliceDensity g f s
        (((R s * y 0 : ℝ) : ℂ) * Complex.exp ((y 1 : ℂ) * Complex.I)) := by
    exact movingKahlerForm_zero_density g f hR
  simp_rw [he]
  exact normalized_polar_integral_eq_disk hpos (sliceDensity_continuousOn g hU hf hmap)

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Manifold
variable {n : ℕ} {X : ComplexManifold n}

theorem moving_disk_area_le (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ}
    {U : Set (ℂ × ℂ)} {V : Set Real3} {J : Set ℝ} {s t C : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hVJ : MapsTo (fun x : Real3 ↦ x 0) V J)
    (hmap : MapsTo (movingPolar R) V U) (hst : s ≤ t)
    (hbox : Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi] ⊆ V)
    (hpos : ∀ x ∈ Icc s t, 0 ≤ R x)
    (hd : ∀ x ∈ Icc s t, deriv R x ≤ -C)
    (hs : ∀ x ∈ Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi],
      metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1,0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0,1)))
    (hleft : MapsTo (fun z : ℂ ↦ ((s : ℂ),z)) (closedBall 0 (R s)) U)
    (hright : MapsTo (fun z : ℂ ↦ ((t : ℂ),z)) (closedBall 0 (R t)) U) :
    curveArea g (fun z ↦ f (t,z)) (ball 0 (R t)) ≤
      curveArea g (fun z ↦ f (s,z)) (ball 0 (R s)) := by
  have hlo : (![s,0,0] : Real3) ≤ ![t,1,2 * Real.pi] := by
    intro i
    fin_cases i <;> simp [hst, Real.pi_pos.le]
  have ha : (![s,0,0] : Real3) ∈ Icc ![s,0,0] ![t,1,2 * Real.pi] := ⟨le_rfl,hlo⟩
  have hb : (![t,1,2 * Real.pi] : Real3) ∈ Icc ![s,0,0] ![t,1,2 * Real.pi] := ⟨hlo,le_rfl⟩
  have hds : DifferentiableAt ℝ R s :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox ha)))
  have hdt : DifferentiableAt ℝ R t :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox hb)))
  have hmono := moving_disk_face_monotone g hU hV hJ hf hR hVJ hmap
    ![s,0,0] ![t,1,2 * Real.pi] hlo hbox rfl rfl rfl rfl C
    (fun x hx ↦ hpos _ ⟨hx.1 0,hx.2 0⟩)
    (fun x hx ↦ hd _ ⟨hx.1 0,hx.2 0⟩) hs
  have hea : ((![s,0,0] : Real3) ∘ (0 : Fin 3).succAbove) = ![0,0] := by
    funext i; fin_cases i <;> rfl
  have heb : ((![t,1,2 * Real.pi] : Real3) ∘ (0 : Fin 3).succAbove) = ![1,2 * Real.pi] := by
    funext i; fin_cases i <;> rfl
  rw [hea, heb] at hmono
  change (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth t y)) ≤
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y)) at hmono
  rw [moving_disk_face_eq_areaIntegral g hU hf hright hdt (hpos t ⟨hst,le_rfl⟩),
    moving_disk_face_eq_areaIntegral g hU hf hleft hds (hpos s ⟨le_rfl,hst⟩)] at hmono
  rw [curveArea_slice_eq_ofReal_integral g hU hf hright,
    curveArea_slice_eq_ofReal_integral g hU hf hleft]
  exact ENNReal.ofReal_le_ofReal hmono

theorem curveArea_slice_ne_top (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z ↦ (s,z)) (closedBall 0 R) U) :
    curveArea g (fun z ↦ f (s,z)) (ball 0 R) ≠ ⊤ := by
  rw [curveArea_slice_eq_ofReal_integral g hU hf hmap]
  exact ENNReal.ofReal_ne_top

end UniversalCoverSplitting

open Set Metric
open scoped ContDiff

namespace UniversalCoverSplitting

def shrinkingRadius (k x : ℝ) : ℝ := k * Real.sqrt (-x)

theorem shrinkingRadius_contDiffOn (k : ℝ) :
    ContDiffOn ℝ ∞ (shrinkingRadius k) (Iio 0) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sqrt (contDiffOn_id.neg)
  intro x hx
  exact ne_of_gt (neg_pos.mpr hx)

theorem shrinkingRadius_hasDerivAt (k : ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (shrinkingRadius k) (-k / (2 * Real.sqrt (-x))) x := by
  exact ((((hasDerivAt_id x).neg).sqrt (ne_of_gt (neg_pos.mpr hx))).const_mul k).congr_deriv
    (by change k * (-1 / (2 * Real.sqrt (-x))) = -k / (2 * Real.sqrt (-x)); ring)

theorem shrinkingRadius_nonneg {k x : ℝ} (hk : 0 ≤ k) :
    0 ≤ shrinkingRadius k x := mul_nonneg hk (Real.sqrt_nonneg _)

theorem exists_shrinkingRadius_deriv_le {k : ℝ} (hk : 0 < k) (C : ℝ) :
    ∃ x₀ : ℝ, x₀ < 0 ∧ ∀ x ∈ Ico x₀ 0, deriv (shrinkingRadius k) x ≤ -C := by
  let d : ℝ := k / (2 * (|C| + 1))
  have hCp : 0 < |C| + 1 := by positivity
  have hdp : 0 < d := div_pos hk (mul_pos (by norm_num) hCp)
  refine ⟨-d^2, neg_neg_of_pos (sq_pos_of_pos hdp), ?_⟩
  intro x hx
  rw [(shrinkingRadius_hasDerivAt k hx.2).deriv]
  have hs : 0 < Real.sqrt (-x) := Real.sqrt_pos.mpr (neg_pos.mpr hx.2)
  have hsd : Real.sqrt (-x) ≤ d := by
    apply (Real.sqrt_le_left hdp.le).mpr
    linarith [hx.1]
  have hmul : C * (2 * Real.sqrt (-x)) ≤ k := by
    calc
      C * (2 * Real.sqrt (-x)) ≤ (|C| + 1) * (2 * Real.sqrt (-x)) := by
        gcongr; exact (le_abs_self C).trans (by linarith)
      _ ≤ (|C| + 1) * (2 * d) := by gcongr
      _ = k := by dsimp [d]; field_simp
  have hp : 0 < 2 * Real.sqrt (-x) := mul_pos (by norm_num) hs
  apply (div_le_iff₀ hp).mpr
  linarith

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric MeasureTheory
open scoped Manifold ContDiff
variable {n : ℕ} {X : ComplexManifold n}

theorem moving_disk_area_le_of_slices (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ} {U : Set (ℂ × ℂ)}
    {J : Set ℝ} {s t C : ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hst : s ≤ t) (hIJ : Icc s t ⊆ J)
    (hpos : ∀ x ∈ Icc s t, 0 ≤ R x)
    (hd : ∀ x ∈ Icc s t, deriv R x ≤ -C)
    (hslices : ∀ x ∈ Icc s t, MapsTo (fun z : ℂ ↦ ((x : ℂ),z))
      (closedBall 0 (R x)) U)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0,1))) :
    curveArea g (fun z ↦ f (t,z)) (ball 0 (R t)) ≤
      curveArea g (fun z ↦ f (s,z)) (ball 0 (R s)) := by
  let W : Set Real3 := (fun x ↦ x 0) ⁻¹' J
  let V : Set Real3 := W ∩ movingPolar R ⁻¹' U
  have hWo : IsOpen W := hJ.preimage (by fun_prop)
  have hpc : ContinuousOn (movingPolar R) W :=
    (movingPolar_contDiffOn hR (fun _ hx ↦ hx)).continuousOn
  have hVo : IsOpen V := hpc.isOpen_inter_preimage hWo hU
  have hbox : Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi] ⊆ V := by
    intro x hx
    have hx0 : x 0 ∈ Icc s t := ⟨hx.1 0,hx.2 0⟩
    have hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1 := ⟨hx.1 1,hx.2 1⟩
    refine ⟨hIJ hx0,hslices _ hx0 ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _ hx0) hx1.1)]
    exact mul_le_of_le_one_right (hpos _ hx0) hx1.2
  exact moving_disk_area_le g hU hVo hJ hf hR (fun _ hx ↦ hx.1)
    (fun _ hx ↦ hx.2) hst hbox hpos hd
    (fun x hx ↦ hs _ (hbox hx).2) (hslices _ ⟨le_rfl,hst⟩)
    (hslices _ ⟨hst,le_rfl⟩)

theorem shrinking_disk_area_bound (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {a k C : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (ha : a < 0) (hk : 0 < k)
    (hslices : ∀ x ∈ Ico a 0, MapsTo (fun z : ℂ ↦ ((x : ℂ),z))
      (closedBall 0 (shrinkingRadius k x)) U)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0,1))) :
    ∃ x₀ ∈ Ico a 0,
      curveArea g (fun z ↦ f (x₀,z)) (ball 0 (shrinkingRadius k x₀)) ≠ ⊤ ∧
      ∀ x ∈ Ico x₀ 0,
        curveArea g (fun z ↦ f (x,z)) (ball 0 (shrinkingRadius k x)) ≤
          curveArea g (fun z ↦ f (x₀,z)) (ball 0 (shrinkingRadius k x₀)) := by
  obtain ⟨b,hb,hbd⟩ := exists_shrinkingRadius_deriv_le hk C
  let x₀ := max a b
  have hx₀ : x₀ ∈ Ico a 0 := ⟨le_max_left _ _,max_lt ha hb⟩
  refine ⟨x₀,hx₀,curveArea_slice_ne_top g hU hf (hslices _ hx₀),?_⟩
  intro x hx
  apply moving_disk_area_le_of_slices g hU isOpen_Iio hf
    (shrinkingRadius_contDiffOn k) hx.1
    (fun y hy ↦ lt_of_le_of_lt hy.2 hx.2)
    (fun _ _ ↦ shrinkingRadius_nonneg hk.le)
  · intro y hy
    exact hbd y ⟨(le_max_right a b).trans hy.1,hy.2.trans_lt hx.2⟩
  · intro y hy
    exact hslices y ⟨hx₀.1.trans hy.1,hy.2.trans_lt hx.2⟩
  · exact hs

end UniversalCoverSplitting

end

end OAI
