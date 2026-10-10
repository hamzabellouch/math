import OAI.Geometry.Perimeter.Regularity.Space

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem exists_compact_trace_on_bounded {n : ℕ} (S V : Set (Space n))
    (hV : Bornology.IsBounded V) (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∃ F : Space n → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      EqOn F f V ∧ EqOn (surfaceGradient S F) (surfaceGradient S f) V := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hV
  let b : ContDiffBump (0 : Space n) :=
    ⟨|r| + 1, |r| + 2, by positivity, by linarith⟩
  have hb : V ⊆ Metric.ball (0 : Space n) b.rIn := by
    intro x hx
    have hx' := Metric.mem_ball.mp (hr hx)
    change dist x 0 < |r| + 1
    linarith [le_abs_self r]
  refine ⟨fun x ↦ b x * f x, b.contDiff.mul hf, b.hasCompactSupport.mul_right, ?_, ?_⟩
  · intro x hx
    change b x * f x = f x
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall (hb hx)), one_mul]
  · intro x hx
    apply surfaceGradient_congr_trace
      ((b.contDiff.mul hf).differentiable (by norm_num) x)
      (hf.differentiable (by norm_num) x)
    filter_upwards [b.eventuallyEq_one_of_mem_ball (hb hx)] with y hy
    intro _
    simp only [hy, Pi.one_apply, one_mul]

theorem exists_compact_approximants_of_mem_sobolevGraph {n : ℕ} (S V : Set (Space n))
    (hV : Bornology.IsBounded V) (hVm : MeasurableSet V)
    {h : Space n → ℝ} {G : Space n → Space n}
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    (hp : (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V)) :
    ∃ φ : ℕ → Space n → ℝ, (∀ j, ContDiff ℝ ∞ (φ j) ∧ HasCompactSupport (φ j)) ∧
      ∃ (hφ : ∀ j, MemLp (φ j) 2 ((surfaceMeasure S).restrict V))
        (hDφ : ∀ j, MemLp (surfaceGradient S (φ j)) 2 ((surfaceMeasure S).restrict V)),
        Tendsto (fun j ↦ ((hφ j).toLp (φ j),
          (hDφ j).toLp (surfaceGradient S (φ j)))) atTop (𝓝 (hh.toLp h, hG.toLp G)) := by
  classical
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp hp
  have hw : ∀ j, ∃ φ : Space n → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      ∃ (hφ : MemLp φ 2 ((surfaceMeasure S).restrict V))
        (hDφ : MemLp (surfaceGradient S φ) 2 ((surfaceMeasure S).restrict V)),
        z j = (hφ.toLp φ, hDφ.toLp (surfaceGradient S φ)) := by
    intro j
    obtain ⟨f, hf, hfmem, hDfmem, hzj⟩ := hz j
    obtain ⟨F, hF, hFc, hFe, hFDe⟩ := exists_compact_trace_on_bounded S V hV f hf
    have he : F =ᵐ[(surfaceMeasure S).restrict V] f :=
      (ae_restrict_mem hVm).mono (fun x hx ↦ hFe hx)
    have hDe : surfaceGradient S F =ᵐ[(surfaceMeasure S).restrict V] surfaceGradient S f :=
      (ae_restrict_mem hVm).mono (fun x hx ↦ hFDe hx)
    let hFm := MemLp.ae_eq he.symm hfmem
    let hDFm := MemLp.ae_eq hDe.symm hDfmem
    refine ⟨F, hF, hFc, hFm, hDFm, hzj.trans ?_⟩
    exact Prod.ext (hfmem.toLp_congr hFm he.symm) (hDfmem.toLp_congr hDFm hDe.symm)
  choose φ hφsmooth hφcompact hφ hDφ hzφ using hw
  refine ⟨φ, fun j ↦ ⟨hφsmooth j, hφcompact j⟩, hφ, hDφ, ?_⟩
  have hzfun : z = (fun j ↦ ((hφ j).toLp (φ j),
      (hDφ j).toLp (surfaceGradient S (φ j)))) := funext hzφ
  rw [← hzfun]
  exact hzt

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI

section BallCutoffs
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

noncomputable def modelCapacityBump : ContDiffBump (0 : V) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

noncomputable def ballCapacityCutoff (c : V) (r : ℝ) (x : V) : ℝ :=
  1 - modelCapacityBump V (r⁻¹ • (x - c))

theorem ballCapacityCutoff_contDiff (c : V) (r : ℝ) :
    ContDiff ℝ ∞ (ballCapacityCutoff V c r) := by
  apply contDiff_const.sub
  apply (modelCapacityBump V).contDiff.comp
  fun_prop

theorem ballCapacityCutoff_mem_Icc (c : V) (r : ℝ) (x : V) :
    ballCapacityCutoff V c r x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (modelCapacityBump V).le_one
  · exact sub_le_self _ (modelCapacityBump V).nonneg

theorem ballCapacityCutoff_zero {c x : V} {r : ℝ} (hr : 0 < r)
    (hx : dist x c ≤ r) : ballCapacityCutoff V c r x = 0 := by
  unfold ballCapacityCutoff
  rw [(modelCapacityBump V).one_of_mem_closedBall, sub_self]
  change dist (r⁻¹ • (x - c)) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    ← div_eq_inv_mul, ← dist_eq_norm]
  exact (div_le_one hr).mpr hx

theorem ballCapacityCutoff_one {c x : V} {r : ℝ} (hr : 0 < r)
    (hx : 2 * r ≤ dist x c) : ballCapacityCutoff V c r x = 1 := by
  unfold ballCapacityCutoff
  rw [(modelCapacityBump V).zero_of_le_dist, sub_zero]
  change 2 ≤ dist (r⁻¹ • (x - c)) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    ← div_eq_inv_mul, ← dist_eq_norm]
  exact (le_div_iff₀ hr).mpr hx

theorem exists_ballCapacityCutoff_gradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : V) (r : ℝ), 0 < r →
      ∀ x : V, ‖gradient (ballCapacityCutoff V c r) x‖ ≤ C / r := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (modelCapacityBump V).hasCompactSupport
    (show ContDiff ℝ 1 (modelCapacityBump V) from (modelCapacityBump V).contDiff) one_ne_zero
  let C : ℝ := (L : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c r hr x
  have hlip : LipschitzWith ⟨C / r, div_nonneg hC.le hr.le⟩ (ballCapacityCutoff V c r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hd : dist (r⁻¹ • (y - c)) (r⁻¹ • (z - c)) = r⁻¹ * dist y z := by
      simp only [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    have hbound := hL.dist_le_mul (r⁻¹ • (y - c)) (r⁻¹ • (z - c))
    rw [hd] at hbound
    have heq : dist (ballCapacityCutoff V c r y) (ballCapacityCutoff V c r z) =
        dist (modelCapacityBump V (r⁻¹ • (y - c)))
          (modelCapacityBump V (r⁻¹ • (z - c))) := by
      simp only [ballCapacityCutoff, dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
    rw [heq]
    change _ ≤ (C / r) * dist y z
    calc
      _ ≤ (L : ℝ) * (r⁻¹ * dist y z) := hbound
      _ = ((L : ℝ) / r) * dist y z := by ring
      _ ≤ (C / r) * dist y z := by
        gcongr
        dsimp [C]
        linarith
  have hb : ‖fderiv ℝ (ballCapacityCutoff V c r) x‖ ≤ C / r :=
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hlip
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hb

theorem ballCapacityCutoff_gradient_zero {c x : V} {r : ℝ} (hr : 0 < r)
    (hx : 2 * r ≤ dist x c) : gradient (ballCapacityCutoff V c r) x = 0 := by
  have hmax : IsLocalMax (ballCapacityCutoff V c r) x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [ballCapacityCutoff_one V hr hx]
    exact (ballCapacityCutoff_mem_Icc V c r y).2
  simp only [gradient, hmax.fderiv_eq_zero, map_zero]

end BallCutoffs

section SmoothAggregate
variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

noncomputable def capacityGate : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def bumpScore (s : Finset ι) (b : ι → V → ℝ) (x : V) : ℝ :=
  ∑ j ∈ s, (b j x) ^ 2

noncomputable def smoothCutoffAggregate (s : Finset ι) (b : ι → V → ℝ) (x : V) : ℝ :=
  capacityGate (bumpScore s b x)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem bumpScore_nonneg [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (b : ι → V → ℝ) (x : V) :
    0 ≤ bumpScore s b x := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

omit [FiniteDimensional ℝ V] in
theorem smoothCutoffAggregate_contDiff [FiniteDimensional ℝ V]
    (s : Finset ι) (b : ι → V → ℝ)
    (hb : ∀ j ∈ s, ContDiff ℝ ∞ (b j)) :
    ContDiff ℝ ∞ (smoothCutoffAggregate s b) := by
  apply capacityGate.contDiff.comp
  exact ContDiff.sum (fun j hj ↦ (hb j hj).pow 2)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem smoothCutoffAggregate_mem_Icc [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (b : ι → V → ℝ) (x : V) :
    smoothCutoffAggregate s b x ∈ Icc (0 : ℝ) 1 :=
  ⟨capacityGate.nonneg, capacityGate.le_one⟩

theorem smoothCutoffAggregate_zero {s : Finset ι} {b : ι → V → ℝ} {x : V}
    (hx : 1 ≤ bumpScore s b x) : smoothCutoffAggregate s b x = 0 := by
  apply capacityGate.zero_of_le_dist
  change 1 ≤ dist (bumpScore s b x) 0
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (bumpScore_nonneg s b x)] using hx

theorem smoothCutoffAggregate_zero_of_one {s : Finset ι} {b : ι → V → ℝ} {x : V}
    {j : ι} (hj : j ∈ s) (hbx : b j x = 1) : smoothCutoffAggregate s b x = 0 := by
  apply smoothCutoffAggregate_zero
  have ht := Finset.single_le_sum (s := s) (f := fun j ↦ b j x ^ 2)
    (fun i hi ↦ sq_nonneg _) hj
  change 1 ≤ ∑ j ∈ s, b j x ^ 2
  simpa only [hbx, one_pow] using ht

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem smoothCutoffAggregate_one [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Finset ι} {b : ι → V → ℝ} {x : V}
    (hx : ∀ j ∈ s, b j x = 0) : smoothCutoffAggregate s b x = 1 := by
  have hscore : bumpScore s b x = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hx j hj]
  unfold smoothCutoffAggregate
  rw [hscore]
  exact capacityGate.one_of_mem_closedBall (by norm_num [capacityGate])

theorem norm_sum_smul_sq_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (s : Finset ι) (a : ι → ℝ) (v : ι → W) :
    ‖∑ j ∈ s, a j • v j‖ ^ 2 ≤
      (∑ j ∈ s, (a j) ^ 2) * (∑ j ∈ s, ‖v j‖ ^ 2) := by
  have ht : ‖∑ j ∈ s, a j • v j‖ ≤ ∑ j ∈ s, |a j| * ‖v j‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le s (fun j ↦ a j • v j)
  calc
    _ ≤ (∑ j ∈ s, |a j| * ‖v j‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
        (fun _ _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)))).mpr ht
    _ ≤ (∑ j ∈ s, |a j| ^ 2) * (∑ j ∈ s, ‖v j‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun j ↦ |a j|) (fun j ↦ ‖v j‖)
    _ = _ := by simp only [sq_abs]

omit [FiniteDimensional ℝ V] in
theorem bumpScore_fderiv [FiniteDimensional ℝ V] (s : Finset ι) (b : ι → V → ℝ) {x : V}
    (hb : ∀ j ∈ s, DifferentiableAt ℝ (b j) x) :
    fderiv ℝ (bumpScore s b) x = ∑ j ∈ s, (2 * b j x) • fderiv ℝ (b j) x := by
  have hd : HasFDerivAt (bumpScore s b)
      (∑ j ∈ s, (2 * b j x) • fderiv ℝ (b j) x) x := by
    have h := HasFDerivAt.sum (fun j hj ↦ (hb j hj).hasFDerivAt.pow 2)
    convert! h using 1
    · ext y; simp only [bumpScore, Finset.sum_apply]
    · simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
  exact hd.fderiv

theorem bumpScore_norm_fderiv_sq_le (s : Finset ι) (b : ι → V → ℝ) {x : V}
    (hb : ∀ j ∈ s, DifferentiableAt ℝ (b j) x) :
    ‖fderiv ℝ (bumpScore s b) x‖ ^ 2 ≤
      4 * bumpScore s b x * ∑ j ∈ s, ‖fderiv ℝ (b j) x‖ ^ 2 := by
  rw [bumpScore_fderiv s b hb]
  have h := norm_sum_smul_sq_le s (fun j ↦ 2 * b j x) (fun j ↦ fderiv ℝ (b j) x)
  convert! h using 1
  congr 1
  simp only [bumpScore, mul_pow, ← Finset.mul_sum]
  norm_num

theorem exists_smoothCutoffAggregate_gradient_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Finset ι) (b : ι → V → ℝ),
      (∀ j ∈ s, ContDiff ℝ 1 (b j)) → ∀ x : V,
      ‖gradient (smoothCutoffAggregate s b) x‖ ^ 2 ≤
        B * ∑ j ∈ s, ‖gradient (b j) x‖ ^ 2 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    capacityGate.hasCompactSupport (show ContDiff ℝ 1 capacityGate from capacityGate.contDiff)
    one_ne_zero
  let B : ℝ := 4 * ((L : ℝ) + 1) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro s b hb x
  have hgrad : ∀ (f : V → ℝ), ‖gradient f x‖ = ‖fderiv ℝ f x‖ := fun _ ↦ by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  simp only [hgrad]
  by_cases hs : 1 ≤ bumpScore s b x
  · have hmin : IsLocalMin (smoothCutoffAggregate s b) x := by
      apply Filter.Eventually.of_forall
      intro y
      rw [smoothCutoffAggregate_zero hs]
      exact (smoothCutoffAggregate_mem_Icc s b y).1
    rw [hmin.fderiv_eq_zero, norm_zero, zero_pow (by decide)]
    exact mul_nonneg hB.le (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · have hdiff : ∀ j ∈ s, DifferentiableAt ℝ (b j) x := fun j hj ↦
      (hb j hj).differentiable one_ne_zero |>.differentiableAt
    have hsdiff : DifferentiableAt ℝ (bumpScore s b) x := by
      convert! DifferentiableAt.sum (fun j hj ↦ (hdiff j hj).pow 2) using 1
      ext y; simp only [bumpScore, Finset.sum_apply, Pi.pow_apply]
    have hcomp : fderiv ℝ (smoothCutoffAggregate s b) x =
        (fderiv ℝ capacityGate (bumpScore s b x)).comp (fderiv ℝ (bumpScore s b) x) :=
      fderiv_comp x ((show ContDiff ℝ 1 capacityGate from capacityGate.contDiff).differentiable
        one_ne_zero).differentiableAt hsdiff
    have hdL : ‖fderiv ℝ capacityGate (bumpScore s b x)‖ ≤ (L : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hL
    have hd : ‖fderiv ℝ (smoothCutoffAggregate s b) x‖ ≤
        (L : ℝ) * ‖fderiv ℝ (bumpScore s b) x‖ := by
      rw [hcomp]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hdL (norm_nonneg _))
    have hdsq := bumpScore_norm_fderiv_sq_le s b hdiff
    have hnnsum : 0 ≤ ∑ j ∈ s, ‖fderiv ℝ (b j) x‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    calc
      _ ≤ ((L : ℝ) * ‖fderiv ℝ (bumpScore s b) x‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr hd
      _ = (L : ℝ) ^ 2 * ‖fderiv ℝ (bumpScore s b) x‖ ^ 2 := mul_pow _ _ _
      _ ≤ (L : ℝ) ^ 2 * (4 * bumpScore s b x * ∑ j ∈ s, ‖fderiv ℝ (b j) x‖ ^ 2) := by
        gcongr
      _ ≤ B * ∑ j ∈ s, ‖fderiv ℝ (b j) x‖ ^ 2 := by
        dsimp [B]
        have hscore : bumpScore s b x ≤ 1 := le_of_not_ge hs
        have hLpos := L.coe_nonneg
        nlinarith [mul_nonneg (sq_nonneg (L : ℝ)) hnnsum,
          mul_le_mul_of_nonneg_left hscore (sq_nonneg (L : ℝ))]

end SmoothAggregate

section Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def smoothDirichletEnergy (μ : Measure V) (f : V → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ

theorem smoothDirichletEnergy_le_ball (μ : Measure V) (f : V → ℝ)
    (c : V) (r L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x, ‖gradient f x‖ ≤ L)
    (hzero : ∀ x, r ≤ dist x c → gradient f x = 0) :
    smoothDirichletEnergy μ f ≤ ENNReal.ofReal (L ^ 2) * μ (Metric.ball c r) := by
  calc
    _ ≤ ∫⁻ x, (Metric.ball c r).indicator (fun _ ↦ ENNReal.ofReal (L ^ 2)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Metric.ball c r
      · rw [Set.indicator_of_mem hx]
        exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) hL).mpr (hbound x))
      · rw [Set.indicator_of_notMem hx]
        simp only [Metric.mem_ball, not_lt] at hx
        simp [hzero x hx]
    _ = _ := by
      rw [lintegral_indicator Metric.isOpen_ball.measurableSet, lintegral_const,
        Measure.restrict_apply_univ]

noncomputable def innerCapacityBump (c : V) (r : ℝ) (x : V) : ℝ :=
  1 - ballCapacityCutoff V c r x

omit [MeasurableSpace V] [BorelSpace V] in
theorem innerCapacityBump_contDiff [MeasurableSpace V] [BorelSpace V] (c : V) (r : ℝ) :
    ContDiff ℝ ∞ (innerCapacityBump c r) :=
  contDiff_const.sub (ballCapacityCutoff_contDiff V c r)

omit [MeasurableSpace V] [BorelSpace V] in
theorem innerCapacityBump_gradient [MeasurableSpace V] [BorelSpace V] (c : V) (r : ℝ) (x : V) :
    gradient (innerCapacityBump c r) x = -gradient (ballCapacityCutoff V c r) x := by
  change gradient (fun y ↦ 1 - ballCapacityCutoff V c r y) x =
    -gradient (ballCapacityCutoff V c r) x
  simp only [gradient, fderiv_const_sub, map_neg]

omit [MeasurableSpace V] [BorelSpace V] in
theorem innerCapacityBump_one [MeasurableSpace V] [BorelSpace V] {c x : V} {r : ℝ} (hr : 0 < r)
    (hx : dist x c ≤ r) : innerCapacityBump c r x = 1 := by
  simp only [innerCapacityBump, ballCapacityCutoff_zero V hr hx, sub_zero]

omit [MeasurableSpace V] [BorelSpace V] in
theorem innerCapacityBump_zero [MeasurableSpace V] [BorelSpace V] {c x : V} {r : ℝ} (hr : 0 < r)
    (hx : 2 * r ≤ dist x c) : innerCapacityBump c r x = 0 := by
  simp only [innerCapacityBump, ballCapacityCutoff_one V hr hx, sub_self]

theorem innerCapacityBump_energy_le (μ : Measure V) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ (c : V) (r : ℝ), 0 < r → ∀ x : V,
      ‖gradient (ballCapacityCutoff V c r) x‖ ≤ C / r)
    (c : V) (r : ℝ) (hr : 0 < r) :
    smoothDirichletEnergy μ (innerCapacityBump c r) ≤
      ENNReal.ofReal ((C / r) ^ 2) * μ (Metric.ball c (2 * r)) := by
  apply smoothDirichletEnergy_le_ball μ _ c (2 * r) (C / r) (by positivity)
  · intro x
    simpa only [innerCapacityBump_gradient, norm_neg] using hbound c r hr x
  · intro x hx
    simp only [innerCapacityBump_gradient, ballCapacityCutoff_gradient_zero V hr hx, neg_zero]

theorem smoothCutoffAggregate_energy_le {ι : Type*} (μ : Measure V)
    {B : ℝ} (hB : 0 ≤ B) (s : Finset ι) (b : ι → V → ℝ)
    (hb : ∀ j ∈ s, ContDiff ℝ 1 (b j))
    (hbound : ∀ x : V, ‖gradient (smoothCutoffAggregate s b) x‖ ^ 2 ≤
      B * ∑ j ∈ s, ‖gradient (b j) x‖ ^ 2) :
    smoothDirichletEnergy μ (smoothCutoffAggregate s b) ≤
      ENNReal.ofReal B * ∑ j ∈ s, smoothDirichletEnergy μ (b j) := by
  have hmeas : ∀ j ∈ s, Measurable (fun x ↦ ENNReal.ofReal (‖gradient (b j) x‖ ^ 2)) := by
    intro j hj
    have hg : Continuous (gradient (b j)) :=
      (InnerProductSpace.toDual ℝ V).symm.continuous.comp
        ((hb j hj).continuous_fderiv one_ne_zero)
    exact (hg.norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal B * ∑ j ∈ s, ENNReal.ofReal (‖gradient (b j) x‖ ^ 2) ∂μ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (‖gradient (smoothCutoffAggregate s b) x‖ ^ 2) ≤
        ENNReal.ofReal B * ∑ j ∈ s, ENNReal.ofReal (‖gradient (b j) x‖ ^ 2)
      rw [← ENNReal.ofReal_sum_of_nonneg (s := s) (f := fun j ↦ ‖gradient (b j) x‖ ^ 2)
        (fun j hj ↦ sq_nonneg _),
        ← ENNReal.ofReal_mul hB]
      exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = _ := by
      rw [lintegral_const_mul (ENNReal.ofReal B) (Finset.measurable_sum s hmeas),
        lintegral_finsetSum s hmeas]
      rfl

end Energy
end RPI

end

end OAI
