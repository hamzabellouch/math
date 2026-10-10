import OAI.Analysis.BernoulliCone.Model

namespace OAI

universe uα uE uF uK uι

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

namespace Test

variable {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}

theorem continuous_gradient (hφ : Test D φ) : Continuous (gradient φ) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
    (hφ.1.continuous_fderiv (by simp))

theorem compact_gradient (hφ : Test D φ) : HasCompactSupport (gradient φ) := by
  exact (hφ.2.1.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ (Space d)).symm)

theorem memLp (hφ : Test D φ) : MemLp φ 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1)

theorem memLp_gradient (hφ : Test D φ) :
    MemLp (gradient φ) 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.continuous_gradient.memLp_of_hasCompactSupport hφ.compact_gradient)

theorem eq_zero_outside (hφ : Test D φ) {x : Space d} (hx : x ∉ D) : φ x = 0 := by
  by_contra h
  exact hx (hφ.2.2 (subset_tsupport φ (by exact h)))

theorem weakGradient (hφ : Test D φ) : WeakGradient D φ (gradient φ) := by
  intro ψ hψ h
  have hcφ : Continuous (fun x => (fderiv ℝ φ x) h) := (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcψ : Continuous (fun x => (fderiv ℝ ψ x) h) := (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  simp_rw [inner_gradient_left]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hφ.eq_zero_outside hx, zero_mul])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hψ.eq_zero_outside hx, mul_zero])]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hcφ.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  · exact (hφ.1.continuous.mul hcψ).integrable_of_hasCompactSupport
      hφ.2.1.mul_right
  · exact (hφ.1.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  · exact fun x _ => hφ.1.differentiable (by simp) x
  · exact fun x _ => hψ.1.differentiable (by simp) x

theorem h1 (hφ : Test D φ) : H1 D φ (gradient φ) :=
  ⟨hφ.memLp, hφ.memLp_gradient, hφ.weakGradient⟩

theorem h10 (hφ : Test D φ) : H10 D φ (gradient φ) := by
  refine ⟨hφ.h1, fun ε hε => ⟨φ, hφ, ?_, ?_⟩⟩
  · simpa using (ENNReal.ofReal_pos.mpr hε)
  · simpa using (ENNReal.ofReal_pos.mpr hε)

end Test

section SobolevLinear
variable {d : ℕ} {D : Set (Space d)}
variable {u v : Space d → ℝ} {G V : Space d → Space d}

lemma memLp_inner_const (hG : MemLp G 2 (volume.restrict D)) (h : Space d) :
    MemLp (fun x => inner ℝ (G x) h) 2 (volume.restrict D) := by
  apply hG.of_le_mul (c := ‖h‖) (hG.aestronglyMeasurable.inner aestronglyMeasurable_const)
  exact Filter.Eventually.of_forall (fun x => by
    simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (G x) h))

lemma Test.memLp_directional {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    MemLp (fun x => (fderiv ℝ φ x) h) 2 (volume.restrict D) := by
  simpa only [inner_gradient_left] using memLp_inner_const hφ.memLp_gradient h

lemma integrable_deriv_product (hu : MemLp u 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => u x * (fderiv ℝ φ x) h) (volume.restrict D) := by
  exact hu.integrable_mul (hφ.memLp_directional h)

lemma integrable_inner_test (hG : MemLp G 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => inner ℝ (G x) h * φ x) (volume.restrict D) := by
  exact (memLp_inner_const hG h).integrable_mul hφ.memLp

lemma H1.add (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x + v x) (fun x => G x + V x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  intro φ hφ h
  simp_rw [add_mul, inner_add_left]
  rw [integral_add (integrable_deriv_product hu.1 hφ h)
      (integrable_deriv_product hv.1 hφ h)]
  simp_rw [add_mul]
  rw [integral_add (integrable_inner_test hu.2.1 hφ h)
      (integrable_inner_test hv.2.1 hφ h), hu.2.2 φ hφ h, hv.2.2 φ hφ h]
  ring

lemma H1.const_smul (hu : H1 D u G) (t : ℝ) :
    H1 D (fun x => t * u x) (fun x => t • G x) := by
  refine ⟨hu.1.const_mul t, hu.2.1.const_smul t, ?_⟩
  intro φ hφ h
  simp_rw [real_inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul, hu.2.2 φ hφ h]
  ring

end SobolevLinear

section Variations
variable {d : ℕ} {D : Set (Space d)}

lemma Test.const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    Test D (fun x => t * φ x) := by
  exact ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left,
    tsupport_mul_subset_right.trans hφ.2.2⟩

lemma Test.gradient_const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    gradient (fun x => t * φ x) = fun x => t • gradient φ x := by
  funext x
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left,
    fderiv_const_mul (hφ.1.differentiable (by simp) x)]
  rfl

lemma Test.h10_const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    H10 D (fun x => t * φ x) (fun x => t • gradient φ x) := by
  rw [← hφ.gradient_const_mul t]
  exact (hφ.const_mul t).h10

lemma integrable_phase {μ : Measure (Space d)} [IsFiniteMeasure μ]
    {u : Space d → ℝ} (hu : AEStronglyMeasurable u μ) :
    Integrable (fun x => if 0 < u x then (1 : ℝ) else 0) μ := by
  have hm : Measurable (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (integrable_const (1 : ℝ)).mono'
    (hm.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖(if 0 < u x then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> norm_num)

lemma integrable_inner_of_memLp {μ : Measure (Space d)}
    {G V : Space d → Space d} (hG : MemLp G 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun x => inner ℝ (G x) (V x)) μ := by
  apply (hG.norm.integrable_mul hV.norm).mono'
    (hG.aestronglyMeasurable.inner hV.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => norm_inner_le_norm (G x) (V x))

lemma energy_affine [IsFiniteMeasure (volume.restrict D)]
    {u φ : Space d → ℝ} {G V : Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D))
    (hG : MemLp G 2 (volume.restrict D))
    (hV : MemLp V 2 (volume.restrict D)) (t : ℝ)
    (hphase : ∀ᵐ x ∂volume.restrict D, (0 < u x + t * φ x) ↔ 0 < u x) :
    energy D (fun x => u x + t * φ x) (fun x => G x + t • V x) =
      energy D u G + 2 * t * (∫ x in D, inner ℝ (G x) (V x)) +
        t ^ 2 * (∫ x in D, ‖V x‖ ^ 2) := by
  have hG2 : Integrable (fun x => ‖G x‖ ^ 2) (volume.restrict D) :=
    hG.integrable_norm_pow (by norm_num)
  have hV2 : Integrable (fun x => ‖V x‖ ^ 2) (volume.restrict D) :=
    hV.integrable_norm_pow (by norm_num)
  have hGV := integrable_inner_of_memLp hG hV
  have hI := integrable_phase hu.aestronglyMeasurable
  have hid : ∀ᵐ x ∂volume.restrict D,
      ‖G x + t • V x‖ ^ 2 + (if 0 < u x + t * φ x then (1 : ℝ) else 0) =
      ((‖G x‖ ^ 2 + (if 0 < u x then (1 : ℝ) else 0)) +
        (2 * t) * inner ℝ (G x) (V x)) + t ^ 2 * ‖V x‖ ^ 2 := by
    filter_upwards [hphase] with x hx
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, if_congr hx rfl rfl]
    ring
  unfold energy
  rw [integral_congr_ae hid]
  have hsum := integral_add ((hG2.add hI).add (hGV.const_mul (2 * t)))
    (hV2.const_mul (t ^ 2))
  have hsum' := integral_add (hG2.add hI) (hGV.const_mul (2 * t))
  simp only [Pi.add_apply] at hsum hsum'
  rw [hsum, hsum', integral_const_mul, integral_const_mul]

lemma linear_coefficient_eq_zero (A B : ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t : ℝ, |t| < ε → 0 ≤ 2 * t * A + t ^ 2 * B) : A = 0 := by
  have hm : IsLocalMin (fun t : ℝ => 2 * t * A + t ^ 2 * B) 0 := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, fun t ht => ?_⟩
    simpa using h t (by simpa [Real.dist_eq] using ht)
  have hd : HasDerivAt (fun t : ℝ => 2 * t * A + t ^ 2 * B) (2 * A) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const A).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const B) using 1
    · rfl
    · norm_num
  have := hm.hasDerivAt_eq_zero hd
  linarith

/-- The first variation for compact perturbations whose support stays uniformly
inside the positive phase. This is derived from full Sobolev comparison. -/
lemma firstVariation_of_comparison [IsFiniteMeasure (volume.restrict D)]
    {u φ : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) (hu0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x)
    (hmin : ∀ (v : Space d → ℝ) (V : Space d → Space d),
      H1 D v V → (∀ᵐ x ∂volume.restrict D, 0 ≤ v x) →
      H10 D (fun x => v x - u x) (fun x => V x - G x) →
      energy D u G ≤ energy D v V)
    (hφ : Test D φ) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ᵐ x ∂volume.restrict D, x ∈ tsupport φ → δ ≤ u x) :
    (∫ x in D, inner ℝ (G x) (gradient φ x)) = 0 := by
  obtain ⟨C, hC⟩ := (hφ.1.continuous.norm.bddAbove_range_of_hasCompactSupport
    hφ.2.1.norm)
  have hCB : ∀ x, |φ x| ≤ |C| + 1 := fun x => by
    have hx := hC (mem_range_self x)
    change ‖φ x‖ ≤ C at hx
    rw [Real.norm_eq_abs] at hx
    linarith [le_abs_self C]
  have hCpos : 0 < |C| + 1 := by positivity
  apply linear_coefficient_eq_zero _ _ (div_pos hδ hCpos)
  intro t ht
  have hsmall : |t| * (|C| + 1) < δ := (lt_div_iff₀ hCpos).mp ht
  have hcontrol : ∀ᵐ x ∂volume.restrict D,
      0 ≤ u x + t * φ x ∧ ((0 < u x + t * φ x) ↔ 0 < u x) := by
    filter_upwards [hu0, hpos] with x hx hp
    by_cases hz : φ x = 0
    · simp [hz, hx]
    · have hux : δ ≤ u x := hp (subset_tsupport φ hz)
      have hb : |t * φ x| < δ := by
        rw [abs_mul]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hCB x) (abs_nonneg t)) hsmall
      have ha : 0 < u x + t * φ x := by
        have := neg_abs_le (t * φ x)
        linarith
      exact ⟨ha.le, iff_of_true ha (lt_of_lt_of_le hδ hux)⟩
  have hcomp := hmin (fun x => u x + t * φ x)
    (fun x => G x + t • gradient φ x)
    (hu.add (hφ.h1.const_smul t)) (hcontrol.mono fun _ hx => hx.1)
    (by simpa only [add_sub_cancel_left] using hφ.h10_const_mul t)
  rw [energy_affine hu.1 hu.2.1 hφ.memLp_gradient t
    (hcontrol.mono fun _ hx => hx.2)] at hcomp
  linarith

lemma LocalMinimizer.firstVariation {u : Space d → ℝ} (hu : LocalMinimizer D u) :
    ∃ G : Space d → Space d, H1Loc D u G ∧
      ∀ (c : Space d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ D →
      ∀ φ : Space d → ℝ, Test (Metric.ball c r) φ →
      ∀ δ : ℝ, 0 < δ →
      (∀ᵐ x ∂volume.restrict (Metric.ball c r), x ∈ tsupport φ → δ ≤ u x) →
      (∫ x in Metric.ball c r, inner ℝ (G x) (gradient φ x)) = 0 := by
  obtain ⟨hD, G, hG, hnonneg, hmin⟩ := hu
  refine ⟨G, hG, fun c r hr hB φ hφ δ hδ hp => ?_⟩
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply firstVariation_of_comparison (hG c r hr hB) _ (hmin c r hr hB) hφ hδ hp
  exact ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_closedBall.trans hB) hnonneg

/-- Once a continuous representative is obtained, every test compactly
supported in its positive phase is an admissible two-sided variation. -/
lemma LocalMinimizer.weakHarmonic_of_continuous {u : Space d → ℝ}
    (hu : LocalMinimizer D u) (hc : ContinuousOn u D) :
    ∃ G : Space d → Space d, H1Loc D u G ∧
      ∀ (c : Space d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ D →
      ∀ φ : Space d → ℝ, Test (Metric.ball c r ∩ {x | 0 < u x}) φ →
      (∫ x in Metric.ball c r, inner ℝ (G x) (gradient φ x)) = 0 := by
  obtain ⟨G, hG, hvar⟩ := hu.firstVariation
  refine ⟨G, hG, fun c r hr hB φ hφ => ?_⟩
  have hsub : tsupport φ ⊆ D :=
    fun x hx => hB (Metric.ball_subset_closedBall (hφ.2.2 hx).1)
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport φ, δ ≤ u x := by
    by_cases hn : (tsupport φ).Nonempty
    · obtain ⟨x, hx, hmin⟩ := hφ.2.1.exists_isMinOn hn (hc.mono hsub)
      exact ⟨u x, (hφ.2.2 hx).2, hmin⟩
    · exact ⟨1, zero_lt_one, fun x hx => (hn ⟨x, hx⟩).elim⟩
  obtain ⟨δ, hd, hδ⟩ := hδ
  exact hvar c r hr hB φ ⟨hφ.1, hφ.2.1, fun x hx => (hφ.2.2 hx).1⟩ δ hd
    (Filter.Eventually.of_forall hδ)

lemma OneHomogeneous.everywhere {u : Space d → ℝ}
    (hu : OneHomogeneous u) (hc : Continuous u) (r : ℝ) (hr : 0 < r) :
    ∀ x, u (r • x) = r * u x := by
  have h1 : Continuous (fun x => u (r • x)) := hc.comp (continuous_id.const_smul r)
  have h2 : Continuous (fun x => r * u x) := continuous_const.mul hc
  have hh : (fun x => u (r • x)) = fun x => r * u x :=
    (h1.ae_eq_iff_eq volume h2).mp (hu r hr)
  exact congrFun hh

end Variations

section GradientUniqueness
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ}
    {G V : Space d → Space d}

/-- The explicit gradient witnesses in the Sobolev definition are unique a.e.
This uses Mathlib's fundamental lemma for compact smooth test functions. -/
lemma H1.gradient_unique (hD : IsOpen D) (hG : H1 D u G) (hV : H1 D u V) :
    G =ᵐ[volume.restrict D] V := by
  have hdir : ∀ h : Space d, ∀ᵐ x ∂volume,
      x ∈ D → inner ℝ (G x - V x) h = 0 := by
    intro h
    apply hD.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · apply locallyIntegrableOn_of_locallyIntegrable_restrict
      exact (memLp_inner_const (hG.2.1.sub hV.2.1) h).locallyIntegrable (by norm_num)
    · intro φ hφc hφs hφD
      have hφ : Test D φ := ⟨hφc, hφs, hφD⟩
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := D) (fun x hx => by rw [hφ.eq_zero_outside hx, zero_smul])]
      simp only [smul_eq_mul, inner_sub_left, mul_sub]
      have hGi : Integrable (fun x => φ x * inner ℝ (G x) h) (volume.restrict D) := by
        simpa only [mul_comm] using integrable_inner_test hG.2.1 hφ h
      have hVi : Integrable (fun x => φ x * inner ℝ (V x) h) (volume.restrict D) := by
        simpa only [mul_comm] using integrable_inner_test hV.2.1 hφ h
      rw [integral_sub hGi hVi]
      have h1 := hG.2.2 φ hφ h
      have h2 := hV.2.2 φ hφ h
      simp only [mul_comm (φ _)]
      linarith
  apply (ae_restrict_iff' hD.measurableSet).mpr
  have hcoord : ∀ i : Fin d, ∀ᵐ x ∂volume, x ∈ D → G x i = V x i := by
    intro i
    filter_upwards [hdir (EuclideanSpace.single i 1)] with x hx hxD
    have hi := hx hxD
    simpa [EuclideanSpace.inner_single_right, sub_eq_zero] using hi
  filter_upwards [ae_all_iff.mpr hcoord] with x hx hxD
  apply PiLp.ext; intro i
  exact hx i hxD

end GradientUniqueness

section SobolevClosure
variable {d : ℕ} {D : Set (Space d)}

lemma integral_inner_bound {α : Type uα} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, inner ℝ (f x) (g x) ∂μ) =
      inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [he, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

lemma Test.memLp_smul_const {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    MemLp (fun x => φ x • h) 2 (volume.restrict D) := by
  refine hφ.memLp.of_le_mul (c := ‖h‖)
    (hφ.memLp.aestronglyMeasurable.smul aestronglyMeasurable_const) ?_
  exact ae_of_all _ (fun x => by simp [norm_smul, mul_comm])

/-- Weak H¹ is closed for the actual L² norm on both components. This is
used to zero-extend arbitrary H¹₀ competitors, not just smooth competitors. -/
lemma eq_zero_of_abs_lt {z : ℝ} (h : ∀ ε : ℝ, 0 < ε → |z| < ε) : z = 0 := by
  by_contra hz
  exact lt_irrefl _ (h |z| (abs_pos.mpr hz))

lemma weakGradient_of_approx {u : Space d → ℝ} {G : Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D)) (hG : MemLp G 2 (volume.restrict D))
    (hap : ∀ ε : ℝ, 0 < ε → ∃ v V, H1 D v V ∧
      eLpNorm (fun x => u x-v x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => G x-V x) 2 (volume.restrict D) < ENNReal.ofReal ε) :
    WeakGradient D u G := by
  intro φ hφ h
  let μ := volume.restrict D
  let ψ := fun x => (fderiv ℝ φ x) h
  let Ψ := fun x => φ x • h
  have hψ : MemLp ψ 2 μ := hφ.memLp_directional h
  have hΨ : MemLp Ψ 2 μ := hφ.memLp_smul_const h
  let C := (eLpNorm ψ 2 μ).toReal + (eLpNorm Ψ 2 μ).toReal + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hz : (∫ x in D, u x * ψ x) + (∫ x in D, inner ℝ (G x) h * φ x) = 0 := by
    apply eq_zero_of_abs_lt
    intro ε hε
    let δ := ε / C
    have hδ : 0 < δ := div_pos hε hC
    obtain ⟨v, V, hv, heu, heG⟩ := hap δ hδ
    have heuto : (eLpNorm (fun x => u x-v x) 2 μ).toReal < δ := by
      exact (ENNReal.toReal_lt_toReal (hu.sub hv.1).eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
        heu |>.trans_eq (ENNReal.toReal_ofReal hδ.le)
    have heGto : (eLpNorm (fun x => G x-V x) 2 μ).toReal < δ := by
      exact (ENNReal.toReal_lt_toReal (hG.sub hv.2.1).eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
        heG |>.trans_eq (ENNReal.toReal_ofReal hδ.le)
    have h1 := integral_inner_bound (hu.sub hv.1) hψ
    have h2 := integral_inner_bound (hG.sub hv.2.1) hΨ
    simp only [Real.inner_apply] at h1
    simp only [Ψ, inner_smul_right, mul_comm (φ _)] at h2
    have heq : (∫ x in D, u x * ψ x) + (∫ x in D, inner ℝ (G x) h * φ x) =
        (∫ x in D, (u x-v x)*ψ x) +
          (∫ x in D, inner ℝ (G x-V x) h * φ x) := by
      simp only [sub_mul, inner_sub_left]
      rw [integral_sub (f := fun x => u x * ψ x) (g := fun x => v x * ψ x)
        (hu.integrable_mul hψ) (hv.1.integrable_mul hψ),
        integral_sub (integrable_inner_test hG hφ h) (integrable_inner_test hv.2.1 hφ h)]
      have ht := hv.2.2 φ hφ h
      change (∫ x in D, v x * ψ x) = _ at ht
      linarith
    rw [heq]
    calc
      _ ≤ |∫ x in D, (u x-v x)*ψ x| + |∫ x in D, inner ℝ (G x-V x) h * φ x| := abs_add_le _ _
      _ ≤ (eLpNorm (fun x => u x-v x) 2 μ).toReal * (eLpNorm ψ 2 μ).toReal +
          (eLpNorm (fun x => G x-V x) 2 μ).toReal * (eLpNorm Ψ 2 μ).toReal := add_le_add h1 h2
      _ ≤ δ * (eLpNorm ψ 2 μ).toReal + δ * (eLpNorm Ψ 2 μ).toReal := by
        gcongr
      _ < ε := by
        have hem : δ*C = ε := div_mul_cancel₀ ε hC.ne'
        dsimp [C] at hem
        nlinarith
  linarith

end SobolevClosure

section Localization
variable {d : ℕ} {D E : Set (Space d)}
variable {u v : Space d → ℝ} {G V : Space d → Space d}

lemma WeakGradient.congr (hu : WeakGradient D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    WeakGradient D v V := by
  intro φ hφ h
  have hleft : (∫ x in D, v x * (fderiv ℝ φ x) h) =
      ∫ x in D, u x * (fderiv ℝ φ x) h := by
    apply integral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx]
  have hright : (∫ x in D, inner ℝ (V x) h * φ x) =
      ∫ x in D, inner ℝ (G x) h * φ x := by
    apply integral_congr_ae
    filter_upwards [hGV] with x hx
    rw [hx]
  rw [hleft, hright, hu φ hφ h]

lemma H1.congr (hu : H1 D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    H1 D v V :=
  ⟨hu.1.ae_eq huv, hu.2.1.ae_eq hGV, hu.2.2.congr huv hGV⟩

lemma H10.congr (hu : H10 D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    H10 D v V := by
  refine ⟨hu.1.congr huv hGV, ?_⟩
  intro ε hε
  obtain ⟨φ, hφ, he, heG⟩ := hu.2 ε hε
  refine ⟨φ, hφ, ?_, ?_⟩
  · have heq : (fun x => u x - φ x) =ᵐ[volume.restrict D] (fun x => v x - φ x) :=
      huv.fun_comp (fun z => z) |>.sub (Filter.EventuallyEq.refl _ φ)
    rwa [← eLpNorm_congr_ae heq]
  · have heq : (fun x => G x - gradient φ x) =ᵐ[volume.restrict D]
        (fun x => V x - gradient φ x) := hGV.sub (Filter.EventuallyEq.refl _ (gradient φ))
    rwa [← eLpNorm_congr_ae heq]

lemma Test.fderiv_eq_zero_outside {φ : Space d → ℝ} (hφ : Test D φ)
    {x : Space d} (hx : x ∉ D) : fderiv ℝ φ x = 0 :=
  fderiv_of_notMem_tsupport ℝ (fun h => hx (hφ.2.2 h))

lemma Test.mono {φ : Space d → ℝ} (hφ : Test D φ) (hDE : D ⊆ E) : Test E φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans hDE⟩

lemma H1.mono (hu : H1 E u G) (hDE : D ⊆ E) : H1 D u G := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hDE le_rfl),
    hu.2.1.mono_measure (Measure.restrict_mono hDE le_rfl), ?_⟩
  intro φ hφ h
  have hh := hu.2.2 φ (hφ.mono hDE) h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hφ.mono hDE).fderiv_eq_zero_outside hx]; simp),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hφ.mono hDE).eq_zero_outside hx, mul_zero])] at hh
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hφ.fderiv_eq_zero_outside hx]; simp),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hφ.eq_zero_outside hx, mul_zero])]
  exact hh

lemma Test.mul {φ ψ : Space d → ℝ} (hφ : Test D φ) (hψ : Test D ψ) :
    Test D (fun x => φ x * ψ x) :=
  ⟨hφ.1.mul hψ.1, hφ.2.1.mul_right, (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφ.2.2⟩

lemma Test.memLp_top {φ : Space d → ℝ} (hφ : Test D φ) :
    MemLp φ ∞ (volume.restrict D) :=
  (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).mono_measure Measure.restrict_le_self

lemma Test.memLp_gradient_top {φ : Space d → ℝ} (hφ : Test D φ) :
    MemLp (gradient φ) ∞ (volume.restrict D) :=
  (hφ.continuous_gradient.memLp_of_hasCompactSupport hφ.compact_gradient).mono_measure
    Measure.restrict_le_self

lemma Test.gradient_mul {φ ψ : Space d → ℝ} (hφ : Test D φ) (hψ : Test D ψ)
    (x : Space d) : gradient (fun y => φ y * ψ y) x =
      φ x • gradient ψ x + ψ x • gradient φ x := by
  apply (InnerProductSpace.toDual ℝ (Space d)).injective
  ext h
  change inner ℝ (gradient (fun y => φ y * ψ y) x) h =
    inner ℝ (φ x • gradient ψ x + ψ x • gradient φ x) h
  simp only [inner_add_left, real_inner_smul_left, inner_gradient_left]
  have hh := ((hφ.1.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt.mul
    ((hψ.1.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hh' := hh.fderiv
  change fderiv ℝ (fun y => φ y * ψ y) x = _ at hh'
  rw [hh']
  simp only [add_apply, smul_apply, smul_eq_mul]

lemma H1.mul_test (hu : H1 D u G) {φ : Space d → ℝ} (hφ : Test D φ) :
    H1 D (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  have hum : MemLp (fun x => φ x * u x) 2 (volume.restrict D) :=
    hφ.memLp_top.fun_mul hu.1
  have hGm : MemLp (fun x => φ x • G x) 2 (volume.restrict D) :=
    hφ.memLp_top.smul hu.2.1
  have hgm : MemLp (fun x => u x • gradient φ x) 2 (volume.restrict D) :=
    hu.1.smul hφ.memLp_gradient_top
  refine ⟨hum, hGm.add hgm, ?_⟩
  intro ψ hψ h
  have hi := integrable_deriv_product hum hψ h
  have hij := integrable_inner_test hgm hψ h
  simp only [real_inner_smul_left, inner_gradient_left] at hij
  have hik := integrable_inner_test hGm hψ h
  simp only [real_inner_smul_left] at hik
  have hderiv (x : Space d) :
      u x * (fderiv ℝ (fun y => φ y * ψ y) x) h =
        (φ x * u x) * (fderiv ℝ ψ x) h + (u x * (fderiv ℝ φ x) h) * ψ x := by
    rw [← inner_gradient_left, hφ.gradient_mul hψ,
      inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_gradient_left, inner_gradient_left]
    ring
  have hweak := hu.2.2 _ (hφ.mul hψ) h
  simp_rw [hderiv] at hweak
  rw [integral_add hi hij] at hweak
  have hright (x : Space d) : inner ℝ (G x) h * (φ x * ψ x) =
      (φ x * inner ℝ (G x) h) * ψ x := by ring
  simp_rw [hright] at hweak
  simp only [inner_add_left, real_inner_smul_left, inner_gradient_left, add_mul]
  rw [integral_add hik hij]
  linarith

lemma energy_congr (huv : u =ᵐ[volume.restrict D] v)
    (hGV : G =ᵐ[volume.restrict D] V) : energy D u G = energy D v V := by
  apply integral_congr_ae
  filter_upwards [huv, hGV] with x hx hGx
  rw [hx, hGx]

lemma LocalMinimizer.congr (hu : LocalMinimizer D u)
    (huv : u =ᵐ[volume.restrict D] v) : LocalMinimizer D v := by
  obtain ⟨hD, G, hG, hnonneg, hmin⟩ := hu
  have heq (c : Space d) (r : ℝ) (hsub : Metric.closedBall c r ⊆ D) :
      u =ᵐ[volume.restrict (Metric.ball c r)] v :=
    huv.filter_mono (ae_mono (Measure.restrict_mono
      (Metric.ball_subset_closedBall.trans hsub) le_rfl))
  refine ⟨hD, G, ?_, ?_, ?_⟩
  · intro c r hr hsub
    exact (hG c r hr hsub).congr (heq c r hsub) (Filter.EventuallyEq.refl _ _)
  · filter_upwards [hnonneg, huv] with x hx he
    rwa [← he]
  · intro c r hr hsub q Q hq hqn hzero
    have hz : H10 (Metric.ball c r) (fun x => q x - u x) (fun x => Q x - G x) :=
      hzero.congr ((Filter.EventuallyEq.refl _ q).sub (heq c r hsub).symm)
        (Filter.EventuallyEq.refl _ _)
    have hm := hmin c r hr hsub q Q hq hqn hz
    rwa [energy_congr (heq c r hsub) (Filter.EventuallyEq.refl _ _)] at hm

lemma LocalMinimizer.mono (hu : LocalMinimizer E u) (hD : IsOpen D) (hDE : D ⊆ E) :
    LocalMinimizer D u := by
  obtain ⟨_, G, hG, hnonneg, hmin⟩ := hu
  refine ⟨hD, G, ?_, ?_, ?_⟩
  · intro c r hr hsub
    exact hG c r hr (hsub.trans hDE)
  · exact hnonneg.filter_mono (ae_mono (Measure.restrict_mono hDE le_rfl))
  · intro c r hr hsub
    exact hmin c r hr (hsub.trans hDE)

lemma Test.gradient_eq_zero_outside {φ : Space d → ℝ} (hφ : Test D φ)
    {x : Space d} (hx : x ∉ D) : gradient φ x = 0 := by
  simp [gradient, hφ.fderiv_eq_zero_outside hx]

/-- Zero extension preserves the exact Sobolev norm of a zero-trace
approximation; neither a smooth representative nor a boundary trace theorem
is assumed. -/
lemma H10.zero_extension (hu : H10 D u G) (hD : MeasurableSet D) (hDE : D ⊆ E) :
    H10 E (D.indicator u) (D.indicator G) := by
  have hres : (volume.restrict E).restrict D = volume.restrict D :=
    Measure.restrict_restrict_of_subset hDE
  have hU : MemLp (D.indicator u) 2 (volume.restrict E) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hres]
    exact hu.1.1
  have hW : MemLp (D.indicator G) 2 (volume.restrict E) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hres]
    exact hu.1.2.1
  have hap (ε : ℝ) (hε : 0 < ε) : ∃ φ : Space d → ℝ, Test E φ ∧
      eLpNorm (fun x => D.indicator u x - φ x) 2 (volume.restrict E) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => D.indicator G x - gradient φ x) 2 (volume.restrict E) < ENNReal.ofReal ε := by
    obtain ⟨φ, hφ, hUφ, hGφ⟩ := hu.2 ε hε
    refine ⟨φ, hφ.mono hDE, ?_, ?_⟩
    · have heq : (fun x => D.indicator u x - φ x) = D.indicator (fun x => u x - φ x) := by
        funext x
        by_cases hx : x ∈ D
        · simp [hx]
        · simp [hx, hφ.eq_zero_outside hx]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hD, hres]
      exact hUφ
    · have heq : (fun x => D.indicator G x - gradient φ x) =
          D.indicator (fun x => G x - gradient φ x) := by
        funext x
        by_cases hx : x ∈ D
        · simp [hx]
        · simp [hx, hφ.gradient_eq_zero_outside hx]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hD, hres]
      exact hGφ
  refine ⟨⟨hU, hW, weakGradient_of_approx hU hW ?_⟩, hap⟩
  intro ε hε
  obtain ⟨φ, hφ, hUφ, hGφ⟩ := hap ε hε
  exact ⟨φ, gradient φ, hφ.h1, hUφ, hGφ⟩

lemma eLpNorm_sub_lt_of_two {α : Type uα} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f g h : α → F}
    (_hf : MemLp f 2 μ) (_hg : MemLp g 2 μ) (_hh : MemLp h 2 μ)
    {ε : ℝ} (hε : 0 < ε)
    (hfg : eLpNorm (fun x => f x - g x) 2 μ < ENNReal.ofReal (ε / 2))
    (hgh : eLpNorm (fun x => g x - h x) 2 μ < ENNReal.ofReal (ε / 2)) :
    eLpNorm (fun x => f x - h x) 2 μ < ENNReal.ofReal ε := by
  have heq : (fun x => f x - h x) =
      (fun x => f x - g x) + (fun x => g x - h x) := by
    funext x
    simp
  rw [heq]
  calc
    _ ≤ eLpNorm (fun x => f x - g x) 2 μ +
        eLpNorm (fun x => g x - h x) 2 μ :=
      eLpNorm_add_le (by norm_num)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hfg hgh
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma H10.of_approx (hu : MemLp u 2 (volume.restrict D))
    (hG : MemLp G 2 (volume.restrict D))
    (hap : ∀ ε : ℝ, 0 < ε → ∃ v V, H10 D v V ∧
      eLpNorm (fun x => u x - v x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => G x - V x) 2 (volume.restrict D) < ENNReal.ofReal ε) :
    H10 D u G := by
  refine ⟨⟨hu, hG, weakGradient_of_approx hu hG ?_⟩, ?_⟩
  · intro ε hε
    obtain ⟨v, V, hv, hvu, hVG⟩ := hap ε hε
    exact ⟨v, V, hv.1, hvu, hVG⟩
  · intro ε hε
    obtain ⟨v, V, hv, hvu, hVG⟩ := hap (ε / 2) (by positivity)
    obtain ⟨φ, hφ, hvφ, hVφ⟩ := hv.2 (ε / 2) (by positivity)
    exact ⟨φ, hφ, eLpNorm_sub_lt_of_two hu hv.1.1 hφ.memLp hε hvu hvφ,
      eLpNorm_sub_lt_of_two hG hv.1.2.1 hφ.memLp_gradient hε hVG hVφ⟩

lemma energy_split [IsFiniteMeasure (volume.restrict E)]
    (hu : MemLp u 2 (volume.restrict E)) (hG : MemLp G 2 (volume.restrict E))
    (hD : MeasurableSet D) (hDE : D ⊆ E) :
    energy E u G = energy D u G + energy (E \ D) u G := by
  have hi : Integrable (fun x => ‖G x‖ ^ 2 + if 0 < u x then (1 : ℝ) else 0)
      (volume.restrict E) :=
    (hG.integrable_norm_pow (by norm_num)).add (integrable_phase hu.aestronglyMeasurable)
  have heq : Dᶜ ∩ E = E \ D := by ext x; simp [and_comm]
  unfold energy
  rw [← integral_add_compl hD hi,
    Measure.restrict_restrict_of_subset hDE, Measure.restrict_restrict hD.compl, heq]

lemma GlobalMinimizer.compare_bounded (hu : GlobalMinimizer u) :
    ∃ G : Space d → Space d, H1Loc univ u G ∧
    ∀ D : Set (Space d), MeasurableSet D → Bornology.IsBounded D →
      ∀ (v : Space d → ℝ) (V : Space d → Space d),
        H1 D v V → (∀ᵐ x ∂volume.restrict D, 0 ≤ v x) →
        H10 D (fun x => v x - u x) (fun x => V x - G x) →
        energy D u G ≤ energy D v V := by
  obtain ⟨_, G, hG, hnonneg, hmin⟩ := hu
  refine ⟨G, hG, ?_⟩
  intro D hD hDb v V hv hvn hz
  obtain ⟨r, hr, hDr⟩ := hDb.subset_ball_lt 0 (0 : Space d)
  let B := Metric.ball (0 : Space d) r
  let : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huB : H1 B u G := hG 0 r hr (subset_univ _)
  have hzu : H10 B (D.indicator (fun x => v x - u x))
      (D.indicator (fun x => V x - G x)) := hz.zero_extension hD hDr
  let U : Space d → ℝ := fun x => u x + D.indicator (fun y => v y - u y) x
  let W : Space d → Space d := fun x => G x + D.indicator (fun y => V y - G y) x
  have hUW : H1 B U W := huB.add hzu.1
  have hres : (volume.restrict B).restrict D = volume.restrict D :=
    Measure.restrict_restrict_of_subset hDr
  have hUn : ∀ᵐ x ∂volume.restrict B, 0 ≤ U x := by
    have hun : ∀ᵐ x ∂volume.restrict B, 0 ≤ u x := by
      rw [Measure.restrict_univ] at hnonneg
      exact hnonneg.filter_mono (ae_mono Measure.restrict_le_self)
    have hvn' : ∀ᵐ x ∂(volume.restrict B).restrict D, 0 ≤ v x := by
      rwa [hres]
    have hvimp : ∀ᵐ x ∂volume.restrict B, x ∈ D → 0 ≤ v x :=
      (ae_restrict_iff' hD).mp hvn'
    filter_upwards [hun, hvimp] with x hux hvx
    by_cases hx : x ∈ D
    · simpa [U, hx] using hvx hx
    · simpa [U, hx] using hux
  have hzero : H10 B (fun x => U x - u x) (fun x => W x - G x) :=
    hzu.congr (ae_of_all _ (fun x => by simp [U]))
      (ae_of_all _ (fun x => by simp [W]))
  have hm := hmin 0 r hr (subset_univ _) U W hUW hUn hzero
  change energy B u G ≤ energy B U W at hm
  have hUinside : U =ᵐ[volume.restrict D] v := by
    filter_upwards [ae_restrict_mem hD] with x hx
    simp [U, hx]
  have hWinside : W =ᵐ[volume.restrict D] V := by
    filter_upwards [ae_restrict_mem hD] with x hx
    simp [W, hx]
  have hUoutside : U =ᵐ[volume.restrict (B \ D)] u := by
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff hD)] with x hx
    simp [U, hx.2]
  have hWoutside : W =ᵐ[volume.restrict (B \ D)] G := by
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff hD)] with x hx
    simp [W, hx.2]
  rw [energy_split huB.1 huB.2.1 hD hDr, energy_split hUW.1 hUW.2.1 hD hDr,
    energy_congr hUinside hWinside, energy_congr hUoutside hWoutside] at hm
  linarith

lemma eLpNorm_two_eq_eLpNorm' {α : Type uα} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 2 μ = eLpNorm' f 2 μ := by
  simpa using eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hf

lemma eLpNorm_lt_of_bound {α : Type uα} {F : Type uF} {K : Type uK} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedAddCommGroup K] {μ : Measure α}
    {f : α → F} {g : α → K} {C ε : ℝ} (hC : 0 < C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖g x‖)
    (hg : eLpNorm' g 2 μ < ENNReal.ofReal (ε / C)) :
    eLpNorm' f 2 μ < ENNReal.ofReal ε := by
  have hbound := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul
    (f := f) (g := g) (c := ⟨C, hC.le⟩) (p := 2)
    (by filter_upwards [hb] with x hx; exact_mod_cast hx) (by norm_num)
  calc
    _ ≤ ENNReal.ofReal C * eLpNorm' g 2 μ := by
      rw [ENNReal.ofReal_eq_coe_nnreal hC.le]
      exact hbound
    _ < ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top hg
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne']

lemma eLpNorm_lt_of_bound_of_aestronglyMeasurable
    {α : Type uα} {F : Type uF} {K : Type uK} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedAddCommGroup K] {μ : Measure α}
    {f : α → F} {g : α → K} {C ε : ℝ} (hC : 0 < C)
    (hf : AEStronglyMeasurable f μ)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖g x‖)
    (hg : eLpNorm g 2 μ < ENNReal.ofReal (ε / C)) :
    eLpNorm f 2 μ < ENNReal.ofReal ε := by
  have hg_meas := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_lt hg)
  rw [eLpNorm_two_eq_eLpNorm' hf]
  rw [eLpNorm_two_eq_eLpNorm' hg_meas] at hg
  exact eLpNorm_lt_of_bound hC hb hg

/-- Multiplying an arbitrary zero-trace Sobolev function by a smooth cutoff
preserves zero trace, with the genuine weak product-rule gradient. -/
lemma H10.mul_test (hu : H10 D u G) {φ : Space d → ℝ} (hφ : Test D φ) :
    H10 D (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  obtain ⟨C₀, hC₀⟩ := hφ.1.continuous.norm.bddAbove_range_of_hasCompactSupport hφ.2.1.norm
  obtain ⟨C₁, hC₁⟩ := hφ.continuous_gradient.norm.bddAbove_range_of_hasCompactSupport
    hφ.compact_gradient.norm
  let C := max (max C₀ C₁) 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbφ (x : Space d) : ‖φ x‖ ≤ C :=
    (hC₀ (mem_range_self x)).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hbg (x : Space d) : ‖gradient φ x‖ ≤ C :=
    (hC₁ (mem_range_self x)).trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨hu.1.mul_test hφ, ?_⟩
  intro ε hε
  obtain ⟨ψ, hψ, hψu, hψG⟩ := hu.2 ((ε / 2) / C) (by positivity)
  have huφ : eLpNorm (fun x => φ x * (u x - ψ x)) 2 (volume.restrict D) <
      ENNReal.ofReal (ε / 2) :=
    eLpNorm_lt_of_bound_of_aestronglyMeasurable hC
      (hφ.memLp.aestronglyMeasurable.mul (hu.1.1.sub hψ.memLp).aestronglyMeasurable)
      (ae_of_all _ fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbφ x) (norm_nonneg _)) hψu
  have hGφ : eLpNorm (fun x => φ x • (G x - gradient ψ x)) 2 (volume.restrict D) <
      ENNReal.ofReal (ε / 2) :=
    eLpNorm_lt_of_bound_of_aestronglyMeasurable hC
      (hφ.memLp.aestronglyMeasurable.smul (hu.1.2.1.sub hψ.memLp_gradient).aestronglyMeasurable)
      (ae_of_all _ fun x => by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hbφ x) (norm_nonneg _)) hψG
  have hug : eLpNorm (fun x => (u x - ψ x) • gradient φ x) 2 (volume.restrict D) <
      ENNReal.ofReal (ε / 2) :=
    eLpNorm_lt_of_bound_of_aestronglyMeasurable hC
      ((hu.1.1.sub hψ.memLp).aestronglyMeasurable.smul hφ.memLp_gradient.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hbg x) (norm_nonneg _)) hψu
  refine ⟨fun x => φ x * ψ x, hφ.mul hψ, ?_, ?_⟩
  · simpa only [mul_sub] using huφ.trans_le (ENNReal.ofReal_le_ofReal (by linarith : ε / 2 ≤ ε))
  · have heq : (fun x => φ x • G x + u x • gradient φ x -
        gradient (fun y => φ y * ψ y) x) =
        (fun x => φ x • (G x - gradient ψ x)) +
        (fun x => (u x - ψ x) • gradient φ x) := by
      funext x
      rw [hφ.gradient_mul hψ]
      simp only [Pi.add_apply, smul_sub, sub_smul]
      abel
    rw [heq]
    calc
      _ ≤ eLpNorm (fun x => φ x • (G x - gradient ψ x)) 2 (volume.restrict D) +
          eLpNorm (fun x => (u x - ψ x) • gradient φ x) 2 (volume.restrict D) :=
        eLpNorm_add_le (by norm_num)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hGφ hug
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Localization
end Bernoulli

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution

namespace Bernoulli.Mollification
open scoped _root_.Bernoulli

variable {d : ℕ}
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
variable {F : Type uF} [NormedAddCommGroup F]

/-- Translation on the actual Lebesgue L² space. -/
def translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    Lp F 2 (volume : Measure (Space d)) :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) f

lemma continuous_translate (f : Lp F 2 (volume : Measure (Space d))) :
    Continuous (translate f) := by
  let shifts : Space d → C(Space d, Space d) :=
    fun y => ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hc : Continuous shifts := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hc
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

lemma coeFn_translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    translate f y =ᵐ[volume] fun x => f (x - y) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume y)

@[simp] lemma translate_zero (f : Lp F 2 (volume : Measure (Space d))) :
    translate f 0 = f := by
  apply Lp.ext
  simpa using coeFn_translate f 0

@[simp] lemma norm_translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    ‖translate f y‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f (measurePreserving_sub_right volume y)

lemma translate_toLp {f : Space d → F} (hf : MemLp f 2 volume) (y : Space d) :
    translate (hf.toLp f) y = (hf.comp_measurePreserving
      (measurePreserving_sub_right volume y)).toLp (fun x => f (x - y)) := by
  apply Lp.ext
  exact (coeFn_translate (hf.toLp f) y).trans
    (((measurePreserving_sub_right volume y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp).trans
      (hf.comp_measurePreserving (measurePreserving_sub_right volume y)).coeFn_toLp.symm)

lemma eLpNorm_translate_tendsto {f : Space d → F} (hf : MemLp f 2 volume) :
    Tendsto (fun y : Space d => eLpNorm (fun x => f (x - y) - f x) 2 volume)
      (𝓝 0) (𝓝 0) := by
  have hn := (((continuous_translate (hf.toLp f)).sub
    (continuous_const (y := hf.toLp f))).continuousAt (x := (0 : Space d))).enorm
  have heq (y : Space d) : ‖translate (hf.toLp f) y - hf.toLp f‖ₑ =
      eLpNorm (fun x => f (x - y) - f x) 2 volume := by
    rw [translate_toLp hf, ← MemLp.toLp_sub, Lp.enorm_toLp]
    rfl
  simpa [ContinuousAt, Pi.sub_apply, heq] using hn

section Inner
variable [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma integrable_inner_of_memLp {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {f g : α → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (ae_of_all _ fun x => norm_inner_le_norm (f x) (g x))

lemma integral_inner_bound {α : Type uα} {K : Type uK} [MeasurableSpace α]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {μ : Measure α} {f g : α → K} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, inner ℝ (f x) (g x) ∂μ) =
      inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [he, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

omit [CompleteSpace F] in
lemma integral_norm_inner_bound {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {f g : α → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ) ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
      integral_mono (integrable_inner_of_memLp hf hg).norm (hf.norm.integrable_mul hg.norm)
        (fun x => norm_inner_le_norm (f x) (g x))
    _ ≤ |∫ x, ‖f x‖ * ‖g x‖ ∂μ| := le_abs_self _
    _ ≤ _ := by
      simpa only [Real.inner_apply, eLpNorm_norm _ hf.aestronglyMeasurable,
        eLpNorm_norm _ hg.aestronglyMeasurable] using integral_inner_bound hf.norm hg.norm

omit [CompleteSpace F] in
/-- The Fubini integrability needed to compare a pointwise convolution with
its Bochner integral in L². The testing function is arbitrary L². -/
lemma integrable_convolution_inner {κ : Space d → ℝ} {f g : Space d → F}
    (hκ : Integrable κ volume) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun p : Space d × Space d =>
      inner ℝ (κ p.2 • f (p.1 - p.2)) (g p.1)) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : Space d × Space d =>
      inner ℝ (κ p.2 • f (p.1 - p.2)) (g p.1)) (volume.prod volume) :=
    (hκ.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      hf.aestronglyMeasurable).inner
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  rw [integrable_prod_iff' hmeas]
  have hft (y : Space d) : MemLp (fun x => f (x - y)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_sub_right volume y)
  refine ⟨ae_of_all _ fun y => ?_, ?_⟩
  · simpa only [real_inner_smul_left] using
      (integrable_inner_of_memLp (hft y) hg).const_mul (κ y)
  · have hm : AEStronglyMeasurable (fun y : Space d =>
        ∫ x : Space d, ‖inner ℝ (κ y • f (x - y)) (g x)‖) volume :=
      hmeas.prod_swap.norm.integral_prod_right'
    apply Integrable.mono' (hκ.norm.mul_const
      ((eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal)) hm
    apply ae_of_all
    intro y
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    simp_rw [real_inner_smul_left, norm_mul, integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hi := integral_norm_inner_bound (hft y) hg
    have heq : eLpNorm (fun x => f (x - y)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_sub_right volume y)
    rwa [heq] at hi

omit [CompleteSpace F] in
lemma memLp_convolution {κ : Space d → ℝ} {f : Space d → F}
    (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    MemLp (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) 2 volume :=
  (hcκ.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    (hf.locallyIntegrable (by norm_num))).memLp_of_hasCompactSupport
    (hcκ.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcf)

/-- A pointwise mollification is the same element of L² as the Bochner
average of translates. This proof includes the Fubini and representative bridge. -/
lemma convolution_toLp_eq_integral_translate {κ : Space d → ℝ} {f : Space d → F}
    (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    (memLp_convolution hκ hcκ hf hcf).toLp
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) =
      ∫ y, κ y • translate (hf.toLp f) y := by
  have hiκ : Integrable κ volume := hκ.integrable_of_hasCompactSupport hcκ
  have hLpInt : Integrable (fun y => κ y • translate (hf.toLp f) y) volume :=
    (hκ.smul (continuous_translate (hf.toLp f))).integrable_of_hasCompactSupport hcκ.smul_right
  have hce := hcκ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    (hf.locallyIntegrable (by norm_num))
  apply ext_inner_left ℝ
  intro g
  rw [← integral_inner hLpInt g]
  have htrans (y : Space d) : inner ℝ g (translate (hf.toLp f) y) =
      ∫ x, inner ℝ (g x) (f (x - y)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_translate (hf.toLp f) y,
      (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp]
      with x hx hy
    rw [hx]
    exact congrArg (inner ℝ (g x)) hy
  have hFubini : Integrable (fun p : Space d × Space d =>
      inner ℝ (g p.1) (κ p.2 • f (p.1 - p.2))) (volume.prod volume) := by
    simpa only [real_inner_comm] using integrable_convolution_inner hiκ hf (Lp.memLp g)
  calc
    _ = ∫ x, inner ℝ (g x) ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_convolution hκ hcκ hf hcf).coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, ∫ y, inner ℝ (g x) (κ y • f (x - y)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (integral_inner (hce x) (g x)).symm
    _ = ∫ y, ∫ x, inner ℝ (g x) (κ y • f (x - y)) :=
      integral_integral_swap hFubini
    _ = ∫ y, inner ℝ g (κ y • translate (hf.toLp f) y) := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      simp_rw [real_inner_smul_right, integral_const_mul, htrans]

/-- L² convergence of compactly supported mollifications. It applies at
once to the function and its weak gradient, once the weak derivative identity
has been proved. -/
lemma convolution_toLp_tendsto {ι : Type uι} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : Space d)} {f : Space d → F}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    Tendsto (fun i => (memLp_convolution (φ i).continuous_normed
      (φ i).hasCompactSupport_normed hf hcf).toLp
        ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)) l
      (𝓝 (hf.toLp f)) := by
  have hc : Continuous (fun y : Space d => translate (hf.toLp f) (-y)) :=
    (continuous_translate (hf.toLp f)).comp continuous_neg
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hc 0
  have heq (i : ι) :
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => translate (hf.toLp f) (-y))) 0) =
        (memLp_convolution (φ i).continuous_normed (φ i).hasCompactSupport_normed hf hcf).toLp
          ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    rw [convolution_toLp_eq_integral_translate (φ i).continuous_normed
      (φ i).hasCompactSupport_normed hf hcf]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg]
  simpa only [heq, neg_zero, translate_zero] using ht

lemma eLpNorm_convolution_sub_tendsto {ι : Type uι} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : Space d)} {f : Space d → F}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    Tendsto (fun i => eLpNorm
      (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
      2 volume) l (𝓝 0) := by
  have ht := ((convolution_toLp_tendsto hφ hf hcf).sub
    (tendsto_const_nhds (x := hf.toLp f))).enorm
  have heq (i : ι) :
      ‖(memLp_convolution (φ i).continuous_normed (φ i).hasCompactSupport_normed hf hcf).toLp
        ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - hf.toLp f‖ₑ =
      eLpNorm
        (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
        2 volume := by
    rw [← MemLp.toLp_sub, Lp.enorm_toLp]
    rfl
  simpa only [heq, sub_self, enorm_zero] using ht

end Inner

end Bernoulli.Mollification

namespace Bernoulli.SobolevDensity
open scoped _root_.Bernoulli
open scoped Convolution
variable {d : ℕ}

lemma test_reflected {κ : Space d → ℝ} (hκ : Test univ κ) (x : Space d) :
    Test univ (fun y => κ (x - y)) := by
  refine ⟨hκ.1.comp (contDiff_const.sub contDiff_id), ?_, subset_univ _⟩
  exact hκ.2.1.comp_homeomorph (Homeomorph.subLeft x)

lemma fderiv_reflected {κ : Space d → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (x y h : Space d) :
    fderiv ℝ (fun z => κ (x - z)) y h = -(fderiv ℝ κ (x - y) h) := by
  have hd := (hκ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x - z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma gradient_convolution {κ u : Space d → ℝ} {G : Space d → Space d}
    (hκ : Test univ κ) (hu : H1 univ u G) (x : Space d) :
    gradient (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x := by
  have hfu : MemLp u 2 volume := by simpa using hu.1
  have hfG : MemLp G 2 volume := by simpa using hu.2.1
  have hlocu : LocallyIntegrable u volume := hfu.locallyIntegrable (by norm_num)
  have hlocG : LocallyIntegrable G volume := hfG.locallyIntegrable (by norm_num)
  have hκ₁ : ContDiff ℝ 1 κ := hκ.1.of_le (by simp)
  have hder := hκ.2.1.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hlocu hκ₁ x
  have heq : u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ =
      κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := convolution_flip _
  rw [heq] at hder
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left, hder.fderiv,
    convolution_precompR_apply _ hlocu (hκ.2.1.fderiv ℝ)
      (hκ.1.continuous_fderiv (by simp))]
  have hw := hu.2.2 _ (test_reflected hκ x) h
  simp only [Measure.restrict_univ, fderiv_reflected hκ.1, mul_neg,
    integral_neg] at hw
  have hw' := neg_injective hw
  rw [convolution_lsmul_swap, real_inner_comm]
  have hi := hκ.2.1.convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hlocG hκ.1.continuous x
  have hi' : Integrable (fun y => κ (x - y) • G y) volume := hi
  rw [← integral_inner hi']
  simp only [convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    _ = ∫ y, u y * fderiv ℝ κ (x - y) h := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => mul_comm _ _
    _ = ∫ y, inner ℝ (G y) h * κ (x - y) := hw'
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        dsimp only
        rw [real_inner_smul_right, real_inner_comm]
        ring

open scoped Pointwise

lemma tsupport_convolution_subset {κ : Space d → ℝ} {u : Space d → ℝ}
    (hκ : HasCompactSupport κ) (hu : HasCompactSupport u) :
    tsupport (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ⊆ tsupport κ + tsupport u := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (Set.add_subset_add (subset_tsupport κ) (subset_tsupport u))
  · exact (hκ.isCompact.add hu.isCompact).isClosed

lemma tsupport_mollification_subset {u : Space d → ℝ} (hu : HasCompactSupport u)
    (φ : ContDiffBump (0 : Space d)) {δ : ℝ} (hδ : φ.rOut < δ) :
    tsupport (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ⊆
      Metric.thickening δ (tsupport u) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := tsupport_convolution_subset φ.hasCompactSupport_normed hu hx
  rw [φ.tsupport_normed_eq, mem_closedBall_zero_iff] at ha
  apply Metric.mem_thickening_iff.mpr
  refine ⟨b, hb, ?_⟩
  simpa [dist_eq_norm] using ha.trans_lt hδ

/-- A fixed sequence of positive-radius smooth normalized mollifiers. -/
def bumps (d : ℕ) (n : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    apply one_div_lt_one_div_of_lt hn
    nlinarith

lemma bumps_tendsto (d : ℕ) : Tendsto (fun n => (bumps d n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Simultaneous weak-H¹ mollification, including support inside the open
set. The gradient convergence is proved, not demanded of the approximants. -/
lemma h10_of_compact_support {D : Set (Space d)} (hD : IsOpen D)
    {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 univ u G) (hcu : HasCompactSupport u) (hcG : HasCompactSupport G)
    (hsu : tsupport u ⊆ D) : H10 D u G := by
  have huD : H1 D u G := hu.mono (subset_univ D)
  refine ⟨huD, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδD⟩ := hcu.isCompact.exists_thickening_subset_open hD hsu
  have hfu : MemLp u 2 volume := by simpa using hu.1
  have hfG : MemLp G 2 volume := by simpa using hu.2.1
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have htu := Mollification.eLpNorm_convolution_sub_tendsto (bumps_tendsto d) hfu hcu
  have htG := Mollification.eLpNorm_convolution_sub_tendsto (bumps_tendsto d) hfG hcG
  have hst : ∀ᶠ n : ℕ in atTop,
      (bumps d n).rOut < δ ∧
      eLpNorm (fun x => ((bumps d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
        2 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => ((bumps d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x - G x)
        2 volume < ENNReal.ofReal ε := by
    exact ((bumps_tendsto d).eventually_lt_const hδ).and
      ((htu.eventually_lt_const hε').and (htG.eventually_lt_const hε'))
  obtain ⟨n, hnδ, hnu, hnG⟩ := hst.exists
  let κ := (bumps d n).normed volume
  have hκ : Test univ κ :=
    ⟨(bumps d n).contDiff_normed, (bumps d n).hasCompactSupport_normed, subset_univ _⟩
  have hφ : Test D (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
    refine ⟨hκ.2.1.contDiff_convolution_left _ hκ.1 (hfu.locallyIntegrable (by norm_num)),
      hκ.2.1.convolution _ hcu, ?_⟩
    exact (tsupport_mollification_subset hcu (bumps d n) hnδ).trans hδD
  refine ⟨_, hφ, ?_, ?_⟩
  · apply lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
    change eLpNorm (u - (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)) 2 volume < _
    rw [eLpNorm_sub_comm]
    exact hnu
  · simp_rw [gradient_convolution hκ hu]
    apply lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
    change eLpNorm (G - (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G)) 2 volume < _
    rw [eLpNorm_sub_comm]
    exact hnG

end Bernoulli.SobolevDensity

namespace Bernoulli.SobolevDensity
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma memLp_global_of_zero_outside {F : Type uF} [NormedAddCommGroup F]
    {f : Space d → F} (hD : MeasurableSet D) (hf : MemLp f 2 (volume.restrict D))
    (hz : ∀ x ∉ D, f x = 0) : MemLp f 2 volume := by
  have heq : D.indicator f = f := by
    funext x
    by_cases hx : x ∈ D
    · simp [hx]
    · simp [hx, hz x hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hD).mpr hf

/-- A compactly supported smooth cutoff of a local weak H¹ function is a
whole-space weak H¹ function, with the actual product-rule gradient. -/
lemma h1_mul_test_global {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) (hD : MeasurableSet D)
    {φ : Space d → ℝ} (hφ : Test D φ) :
    H1 univ (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  have hφU := hφ.mono (subset_univ D)
  have hzφ (x : Space d) (hx : x ∉ D) : φ x = 0 := hφ.eq_zero_outside hx
  have hzg (x : Space d) (hx : x ∉ D) : gradient φ x = 0 := hφ.gradient_eq_zero_outside hx
  have hum : MemLp (fun x => φ x * u x) 2 volume :=
    memLp_global_of_zero_outside hD (hφ.memLp_top.fun_mul hu.1)
      (fun x hx => by rw [hzφ x hx, zero_mul])
  have hGm : MemLp (fun x => φ x • G x) 2 volume :=
    memLp_global_of_zero_outside hD (hφ.memLp_top.smul hu.2.1)
      (fun x hx => by rw [hzφ x hx, zero_smul])
  have hgm : MemLp (fun x => u x • gradient φ x) 2 volume :=
    memLp_global_of_zero_outside hD (hu.1.smul hφ.memLp_gradient_top)
      (fun x hx => by rw [hzg x hx, smul_zero])
  refine ⟨by simpa using hum, by rw [Measure.restrict_univ]; exact hGm.add hgm, ?_⟩
  intro ψ hψ h
  have hφψ : Test D (fun x => φ x * ψ x) :=
    ⟨hφ.1.mul hψ.1, hφ.2.1.mul_right,
      (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφ.2.2⟩
  have hi := integrable_deriv_product (D := univ) (by simpa using hum) hψ h
  have hij := integrable_inner_test (D := univ) (by simpa using hgm) hψ h
  have hik := integrable_inner_test (D := univ) (by simpa using hGm) hψ h
  simp only [Measure.restrict_univ, real_inner_smul_left, inner_gradient_left] at hi hij hik
  have hderiv (x : Space d) :
      u x * (fderiv ℝ (fun y => φ y * ψ y) x) h =
        (φ x * u x) * (fderiv ℝ ψ x) h + (u x * (fderiv ℝ φ x) h) * ψ x := by
    rw [← inner_gradient_left, hφU.gradient_mul hψ,
      inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_gradient_left, inner_gradient_left]
    ring
  have hweak := hu.2.2 _ hφψ h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφψ.fderiv_eq_zero_outside hx]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφψ.eq_zero_outside hx, mul_zero])] at hweak
  simp_rw [hderiv] at hweak
  rw [integral_add hi hij] at hweak
  have hright (x : Space d) : inner ℝ (G x) h * (φ x * ψ x) =
      (φ x * inner ℝ (G x) h) * ψ x := by ring
  simp_rw [hright] at hweak
  simp only [Measure.restrict_univ, inner_add_left, real_inner_smul_left,
    inner_gradient_left, add_mul]
  rw [integral_add hik hij]
  linarith

lemma h10_mul_test {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) (hD : IsOpen D) {φ : Space d → ℝ} (hφ : Test D φ) :
    H10 D (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  have hcu : HasCompactSupport (fun x => φ x * u x) := hφ.2.1.mul_right
  have hφs : Test (tsupport φ) φ := ⟨hφ.1, hφ.2.1, subset_rfl⟩
  have hcG : HasCompactSupport (fun x => φ x • G x + u x • gradient φ x) := by
    apply HasCompactSupport.intro hφ.2.1.isCompact
    intro x hx
    rw [hφs.eq_zero_outside hx, hφs.gradient_eq_zero_outside hx]
    simp
  have hsu : tsupport (fun x => φ x * u x) ⊆ D :=
    (tsupport_mul_subset_left (f := φ) (g := u)).trans hφ.2.2
  exact h10_of_compact_support hD (h1_mul_test_global hu hD.measurableSet hφ) hcu hcG hsu

end Bernoulli.SobolevDensity

namespace Bernoulli
open scoped _root_.Bernoulli
namespace LipschitzSobolev
variable {d : ℕ} {u : Space d → ℝ} {K : NNReal}

lemma measurable_gradient : Measurable (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ u)

lemma norm_gradient_le (hu : LipschitzWith K u) (x : Space d) :
    ‖gradient u x‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hu

lemma weakGradient (hu : LipschitzWith K u) (D : Set (Space d)) :
    WeakGradient D u (gradient u) := by
  intro φ hφ h
  have hφdiff := hφ.1.differentiable (by simp)
  obtain ⟨C, hφlip⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2.1 (by simp)
  have heq := hu.integral_lineDeriv_mul_eq (μ := volume) hφlip hφ.2.1 h
  have hleft : (fun x => lineDeriv ℝ u x h * φ x) =ᵐ[volume]
      (fun x => inner ℝ (gradient u x) h * φ x) := by
    filter_upwards [hu.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv, inner_gradient_left]
  have hright : (fun x => lineDeriv ℝ φ x (-h) * u x) =
      (fun x => -(u x * (fderiv ℝ φ x) h)) := by
    funext x
    rw [(hφdiff x).lineDeriv_eq_fderiv, map_neg]
    ring
  rw [integral_congr_ae hleft, hright, integral_neg] at heq
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hne : x ∉ tsupport φ := fun hx' => hx (hφ.2.2 hx')
      rw [fderiv_of_notMem_tsupport ℝ hne, zero_apply, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφ.eq_zero_outside hx, mul_zero])]
  linarith

lemma h1_ball (hu : LipschitzWith K u) (c : Space d) (r : ℝ) :
    H1 (Metric.ball c r) u (gradient u) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine ⟨?_, ?_, weakGradient hu _⟩
  · apply MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u c‖ + K * max r 0)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    calc ‖u x‖ ≤ ‖u c‖ + ‖u x - u c‖ := norm_le_insert' _ _
      _ ≤ ‖u c‖ + K * dist x c := by
        gcongr
        simpa only [dist_eq_norm] using hu.norm_sub_le x c
      _ ≤ ‖u c‖ + K * max r 0 := by
        gcongr
        exact (Metric.mem_ball.mp hx).le.trans (le_max_left _ _)
  · exact MemLp.of_bound measurable_gradient.aestronglyMeasurable K
      (Filter.Eventually.of_forall (norm_gradient_le hu))

lemma compact_gradient (hc : HasCompactSupport u) : HasCompactSupport (gradient u) := by
  exact (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ (Space d)).symm)

lemma h1_compact (hu : LipschitzWith K u) (hc : HasCompactSupport u) :
    H1 univ u (gradient u) := by
  refine ⟨by simpa using hu.continuous.memLp_of_hasCompactSupport (p := 2) hc, ?_,
    weakGradient hu _⟩
  rw [Measure.restrict_univ]
  have hzero (x : Space d) (hx : x ∉ tsupport u) : gradient u x = 0 := by
    rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.isCompact.measure_lt_top.ne
  have hmem : MemLp (gradient u) 2 (volume.restrict (tsupport u)) :=
    MemLp.of_bound measurable_gradient.aestronglyMeasurable K
      (Filter.Eventually.of_forall (norm_gradient_le hu))
  have heq : (tsupport u).indicator (gradient u) = gradient u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · simp [hx]
    · simp [hx, hzero x hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport u).measurableSet).mpr hmem

end LipschitzSobolev
end Bernoulli

namespace Bernoulli
open scoped _root_.Bernoulli

lemma H1.sub {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ}
    {G V : Space d → Space d} (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x - v x) (fun x => G x - V x) := by
  simpa only [neg_one_mul, neg_one_smul, sub_eq_add_neg] using hu.add (hv.const_smul (-1))

lemma LipschitzSobolev.h10 {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ}
    {K : NNReal} (hu : LipschitzWith K u) (hc : HasCompactSupport u)
    (hD : IsOpen D) (hs : tsupport u ⊆ D) : H10 D u (gradient u) :=
  SobolevDensity.h10_of_compact_support hD (LipschitzSobolev.h1_compact hu hc) hc
    (LipschitzSobolev.compact_gradient hc) hs

/-- Genuine Sobolev comparison, specialized only AFTER two explicit functions
  have been shown Lipschitz and their difference compactly supported. -/
lemma GlobalMinimizer.compare_lipschitz {d : ℕ} {u v : Space d → ℝ} {K L : NNReal}
    (hm : GlobalMinimizer u) (hu : LipschitzWith K u) (hv : LipschitzWith L v)
    (c : Space d) {r : ℝ} (hr : 0 < r)
    (hn : ∀ᵐ x ∂volume.restrict (Metric.ball c r), 0 ≤ v x)
    (hc : HasCompactSupport (fun x => v x - u x))
    (hs : tsupport (fun x => v x - u x) ⊆ Metric.ball c r) :
    energy (Metric.ball c r) u (gradient u) ≤ energy (Metric.ball c r) v (gradient v) := by
  obtain ⟨_, G, hG, _, hmin⟩ := hm
  have huG := hG c r hr (subset_univ _)
  have hu' := LipschitzSobolev.h1_ball hu c r
  have hv' := LipschitzSobolev.h1_ball hv c r
  have hw := LipschitzSobolev.h10 (hv.sub hu) hc Metric.isOpen_ball hs
  have hweak := hv'.sub huG
  have hgrad := hw.1.gradient_unique Metric.isOpen_ball hweak
  have hh := hmin c r hr (subset_univ _) v (gradient v) hv' hn
    (hw.congr (Filter.EventuallyEq.refl _ _) hgrad)
  rwa [energy_congr (Filter.EventuallyEq.refl _ _) (huG.gradient_unique Metric.isOpen_ball hu')] at hh

end Bernoulli

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

/-- The closure definition itself provides smooth approximants converging
  simultaneously in both L² seminorms. -/
lemma H10_sequence (hu : H10 D u G) :
    ∃ f : ℕ → Space d → ℝ, (∀ n, Test D (f n)) ∧
      Tendsto (fun n => eLpNorm (f n - u) 2 (volume.restrict D)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (f n) - G) 2 (volume.restrict D)) atTop (𝓝 0) := by
  choose f hf hfu hfG using fun n : ℕ => hu.2 (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨f, hf, ?_, ?_⟩
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [ENNReal.ofReal_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    dsimp only [Function.comp_apply]
    rw [eLpNorm_sub_comm]
    exact (hfu n).le
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [ENNReal.ofReal_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    dsimp only [Function.comp_apply]
    rw [eLpNorm_sub_comm]
    exact (hfG n).le

lemma gradient_comp {F : ℝ → ℝ} {f : Space d → ℝ} {x : Space d}
    (hF : DifferentiableAt ℝ F (f x)) (hf : DifferentiableAt ℝ f x) :
    gradient (F ∘ f) x = deriv F (f x) • gradient f x := by
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left, fderiv_comp x hF hf, ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul, real_inner_smul_left, inner_gradient_left]

lemma test_comp_h1 {F : ℝ → ℝ} {K : NNReal} {f : Space d → ℝ}
    (hF : ContDiff ℝ 1 F) (hlip : LipschitzWith K F) (hz : F 0 = 0)
    (hf : Test univ f) : H1 univ (F ∘ f) (fun x => deriv F (f x) • gradient f x) := by
  obtain ⟨L, hL⟩ := hf.1.lipschitzWith_of_hasCompactSupport hf.2.1 (by simp)
  have hm := LipschitzSobolev.h1_compact (hlip.comp hL) (hf.2.1.comp_left hz)
  have heq : gradient (F ∘ f) = fun x => deriv F (f x) • gradient f x := by
    funext x
    exact gradient_comp (hF.differentiable (by simp) _) (hf.1.differentiable (by simp) _)
  rwa [heq] at hm

section Dominated
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

/-- L² dominated convergence, expressed in the same seminorms as `H10`. -/
lemma tendsto_eLpNorm_zero_of_dominated {f : ℕ → α → E} {b : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : MemLp (f n) 2 μ := hb.mono (hf n) (hbound n)
  have hi : Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun x => ‖b x‖ ^ 2)
      (fun n => (hf n).norm.pow 2) (hb.integrable_norm_pow (by norm_num)) ?_ ?_
    · simpa using ht
    · intro n
      filter_upwards [hbound n] with x hx
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [hlim] with x hx
      simpa using hx.norm.pow 2
  have heq (n : ℕ) : eLpNorm (f n) 2 μ =
      ENNReal.ofReal ((∫ x, ‖f n x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    simpa using (hm n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simp_rw [heq]
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hi.rpow_const (Or.inr (by norm_num : 0 ≤ (1 / 2 : ℝ))))
  convert! ht using 1
  simp

end Dominated
end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma test_comp_h10 (hD : IsOpen D) {F : ℝ → ℝ} {K : NNReal} {f : Space d → ℝ}
    (hF : ContDiff ℝ 1 F) (hlip : LipschitzWith K F) (hz : F 0 = 0)
    (hf : Test D f) : H10 D (F ∘ f) (fun x => deriv F (f x) • gradient f x) := by
  obtain ⟨L, hL⟩ := hf.1.lipschitzWith_of_hasCompactSupport hf.2.1 (by simp)
  have hm := LipschitzSobolev.h10 (hlip.comp hL) (hf.2.1.comp_left hz) hD
    ((tsupport_comp_subset hz f).trans hf.2.2)
  have heq : gradient (F ∘ f) = fun x => deriv F (f x) • gradient f x := by
    funext x
    exact gradient_comp (hF.differentiable (by simp) _) (hf.1.differentiable (by simp) _)
  rwa [heq] at hm

lemma h10_of_strong {f : ℕ → Space d → ℝ} {V : ℕ → Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D)) (hG : MemLp G 2 (volume.restrict D))
    (hf : ∀ n, H10 D (f n) (V n))
    (hfu : Tendsto (fun n => eLpNorm (f n - u) 2 (volume.restrict D)) atTop (𝓝 0))
    (hfG : Tendsto (fun n => eLpNorm (V n - G) 2 (volume.restrict D)) atTop (𝓝 0)) :
    H10 D u G := by
  apply H10.of_approx hu hG
  intro ε hε
  have hp : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨n, hn, hn'⟩ := ((hfu.eventually_lt_const hp).and (hfG.eventually_lt_const hp)).exists
  refine ⟨f n, V n, hf n, ?_, ?_⟩
  · change eLpNorm (u - f n) 2 (volume.restrict D) < ENNReal.ofReal ε
    rwa [eLpNorm_sub_comm]
  · change eLpNorm (G - V n) 2 (volume.restrict D) < ENNReal.ofReal ε
    rwa [eLpNorm_sub_comm]

section Nemytskii
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma lipschitz_tendsto_eLpNorm {f : ℕ → α → ℝ} {u : α → ℝ}
    {F : ℝ → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hu : Tendsto (fun n => eLpNorm' (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm' (F ∘ f n - F ∘ u) 2 μ) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul (a := (K : ℝ≥0∞)) hu (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have hbound := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul
    (μ := μ) (f := F ∘ f n - F ∘ u) (g := f n - u) (c := K) (p := 2)
    (Filter.Eventually.of_forall fun x => by exact_mod_cast hF.norm_sub_le (f n x) (u x))
    (by norm_num)
  exact hbound

lemma lipschitz_tendsto_eLpNorm_of_aestronglyMeasurable {f : ℕ → α → ℝ} {u : α → ℝ}
    {F : ℝ → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hu_meas : AEStronglyMeasurable u μ)
    (hu : Tendsto (fun n => eLpNorm (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F ∘ f n - F ∘ u) 2 μ) atTop (𝓝 0) := by
  have hu_raw : Tendsto (fun n => eLpNorm' (f n - u) 2 μ) atTop (𝓝 0) :=
    hu.congr' (Eventually.of_forall fun n => eLpNorm_two_eq_eLpNorm' ((hf n).sub hu_meas))
  apply (lipschitz_tendsto_eLpNorm hF hu_raw).congr'
  exact Eventually.of_forall fun n => (eLpNorm_two_eq_eLpNorm'
    ((hF.continuous.comp_aestronglyMeasurable (hf n)).sub
      (hF.continuous.comp_aestronglyMeasurable hu_meas))).symm

lemma bounded_smul_tendsto {a : ℕ → α → ℝ} {b : α → ℝ} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hG : MemLp G 2 μ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C) (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x))) :
    Tendsto (fun n => eLpNorm (fun x => (a n x-b x) • G x) 2 μ) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_zero_of_dominated (f := fun n x => (a n x - b x) • G x)
    (fun n => ((ha n).sub hb).smul hG.aestronglyMeasurable)
    (hG.norm.const_smul (2*C))
  · intro n
    filter_upwards [hab n, hbb] with x hx hy
    simp only [Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 2*C)]
    have hab' : ‖a n x - b x‖ ≤ 2*C := (norm_sub_le _ _).trans (by linarith)
    exact mul_le_mul_of_nonneg_right hab' (norm_nonneg _)
  · filter_upwards [ht] with x hx
    simpa using (hx.sub_const (b x)).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => G x) atTop (𝓝 (G x)))

end Nemytskii
end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
section Nemytskii
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_smul_strong {a : ℕ → α → ℝ} {b : α → ℝ}
    {V : ℕ → α → E} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hV : ∀ n, MemLp (V n) 2 μ) (hG : MemLp G 2 μ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C) (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hVG : Tendsto (fun n => eLpNorm (V n - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x • V n x - b x • G x) 2 μ)
      atTop (𝓝 0) := by
  have hres := bounded_smul_tendsto ha hb hG hC hab hbb ht
  have hfst := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hVG (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hfst
  have hsum := hfst.add hres
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  have heq : (fun x => a n x • V n x - b x • G x) =
      (fun x => a n x • (V n x-G x)) + (fun x => (a n x-b x) • G x) := by
    funext x
    simp only [Pi.add_apply, smul_sub, sub_smul]
    abel
  dsimp only
  rw [heq]
  apply (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
  apply add_le_add _ le_rfl
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun x => a n x • (V n x - G x)) (g := fun x => V n x - G x)
    ((ha n).smul ((hV n).sub hG).aestronglyMeasurable) ?_ 2
  filter_upwards [hab n] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (V n x - G x))

end Nemytskii
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma h10_comp_C1 (hD : IsOpen D) (hu : H10 D u G)
    {F : ℝ → ℝ} {K : NNReal} (hF : ContDiff ℝ 1 F)
    (hlip : LipschitzWith K F) (hz : F 0 = 0) :
    H10 D (F ∘ u) (fun x => deriv F (u x) • G x) := by
  obtain ⟨f, hf, hfu, hfG⟩ := H10_sequence hu
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) hfu).exists_seq_tendsto_ae
  have hdc := hF.continuous_deriv (by simp)
  have hdermem : MemLp (fun x => deriv F (u x)) ∞ (volume.restrict D) :=
    memLp_top_of_bound (hdc.comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable) K
      (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
  apply h10_of_strong (hlip.comp_memLp hz hu.1.1) (hdermem.smul hu.1.2.1)
    (fun n => test_comp_h10 hD hF hlip hz (hf (ns n)))
  · exact lipschitz_tendsto_eLpNorm_of_aestronglyMeasurable hlip
      (fun n => (hf (ns n)).memLp.aestronglyMeasurable) hu.1.1.aestronglyMeasurable
      (hfu.comp hns.tendsto_atTop)
  · apply bounded_smul_strong
      (fun n => hdc.comp_aestronglyMeasurable (hf (ns n)).memLp.aestronglyMeasurable)
      (hdc.comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
      (fun n => (hf (ns n)).memLp_gradient) hu.1.2.1 K.coe_nonneg
      (fun _ => Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
      (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
      ?_ (hfG.comp hns.tendsto_atTop)
    filter_upwards [hpoint] with x hx
    exact hdc.continuousAt.tendsto.comp hx

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli

def cutSlope (n : ℕ) (t : ℝ) : ℝ := min (max (((n : ℝ)+1)*t) 0) 1

def cutPrimitive (n : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, cutSlope n s

lemma cutSlope_continuous (n : ℕ) : Continuous (cutSlope n) := by
  unfold cutSlope
  fun_prop

lemma cutSlope_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cutSlope n t :=
  le_min (le_max_right _ _) (by norm_num)

lemma cutSlope_le_one (n : ℕ) (t : ℝ) : cutSlope n t ≤ 1 := min_le_right _ _

lemma cutSlope_norm_le (n : ℕ) (t : ℝ) : ‖cutSlope n t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutSlope_nonneg n t)]
  exact cutSlope_le_one n t

lemma cutPrimitive_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (cutPrimitive n) (cutSlope n t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((cutSlope_continuous n).intervalIntegrable _ _)
    (cutSlope_continuous n).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cutSlope_continuous n).continuousAt

lemma cutPrimitive_contDiff (n : ℕ) : ContDiff ℝ 1 (cutPrimitive n) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (cutPrimitive_deriv n t).differentiableAt, ?_⟩
  have heq : deriv (cutPrimitive n) = cutSlope n := funext fun t =>
    (cutPrimitive_deriv n t).deriv
  rw [heq]
  exact cutSlope_continuous n

lemma cutPrimitive_lipschitz (n : ℕ) : LipschitzWith 1 (cutPrimitive n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (cutPrimitive_deriv n t).differentiableAt)
  intro t
  rw [(cutPrimitive_deriv n t).deriv, ← NNReal.coe_le_coe]
  exact cutSlope_norm_le n t

@[simp] lemma cutPrimitive_zero (n : ℕ) : cutPrimitive n 0 = 0 := by
  simp [cutPrimitive]

lemma cutSlope_tendsto (t : ℝ) :
    Tendsto (fun n => cutSlope n t) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  by_cases ht : 0 < t
  · simp only [ite_eq_left ht]
    have hg : Tendsto (fun n : ℕ => ((n : ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_mono (fun n : ℕ => (show (n : ℝ) ≤ (n : ℝ)+1 by linarith))
        tendsto_natCast_atTop_atTop).atTop_mul_const ht
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop 1] with n hn
    dsimp only [cutSlope]
    exact (min_eq_right (hn.trans (le_max_left _ _))).symm
  · simp only [ite_eq_right ht]
    have hf (n : ℕ) : cutSlope n t = 0 := by
      have hm : ((n : ℝ)+1)*t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt ht)
      simp [cutSlope, max_eq_right hm]
    simp_rw [hf]
    exact tendsto_const_nhds

lemma integral_step (t : ℝ) :
    (∫ s in (0 : ℝ)..t, if 0 < s then (1 : ℝ) else 0) = max t 0 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]
    calc
      _ = ∫ _s in (0 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall fun s hs => by
          simp only [uIoc_of_le ht, mem_Ioc] at hs
          simp [hs.1]
      _ = t := by simp
  · rw [max_eq_right ht.le, intervalIntegral.integral_symm]
    have hz : (∫ s in t..(0 : ℝ), if 0 < s then (1 : ℝ) else 0) = 0 := by
      apply intervalIntegral.integral_zero_ae
      exact Filter.Eventually.of_forall fun s hs => by
        simp only [uIoc_of_le ht.le, mem_Ioc] at hs
        simp [not_lt.mpr hs.2]
    simp [hz]

lemma cutPrimitive_tendsto (t : ℝ) :
    Tendsto (fun n => cutPrimitive n t) atTop (𝓝 (max t 0)) := by
  rw [← integral_step t]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun n => (cutSlope_continuous n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun s _ => cutSlope_norm_le n s
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s _ => cutSlope_tendsto s

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma norm_positivePart (t : ℝ) : ‖max t 0‖ ≤ ‖t‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma step_memLp_top (hu : AEStronglyMeasurable u (volume.restrict D)) :
    MemLp (fun x => if 0 < u x then (1 : ℝ) else 0) ∞ (volume.restrict D) := by
  have hs : Measurable (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  apply memLp_top_of_bound (hs.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply]
    split_ifs <;> norm_num

lemma h10_positivePart (hD : IsOpen D) (hu : H10 D u G) :
    H10 D (fun x => max (u x) 0)
      (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x) := by
  have hum : MemLp (fun x => max (u x) 0) 2 (volume.restrict D) := by
    apply hu.1.1.mono ((continuous_id.max continuous_const).comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => norm_positivePart (u x)
  have hg : MemLp (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x)
      2 (volume.restrict D) := (step_memLp_top hu.1.1.aestronglyMeasurable).smul hu.1.2.1
  have hcomp (n : ℕ) : H10 D (cutPrimitive n ∘ u) (fun x => cutSlope n (u x) • G x) := by
    have hh := h10_comp_C1 hD hu (cutPrimitive_contDiff n) (cutPrimitive_lipschitz n)
      (cutPrimitive_zero n)
    have heq : deriv (cutPrimitive n) = cutSlope n :=
      funext fun t => (cutPrimitive_deriv n t).deriv
    rwa [heq] at hh
  apply h10_of_strong hum hg hcomp
  · apply tendsto_eLpNorm_zero_of_dominated
      (f := fun n x => cutPrimitive n (u x) - max (u x) 0)
      (fun n => ((cutPrimitive_lipschitz n).continuous.comp_aestronglyMeasurable
        hu.1.1.aestronglyMeasurable).sub hum.aestronglyMeasurable)
      (hu.1.1.norm.const_smul (2 : ℝ))
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        have hn : ‖cutPrimitive n (u x)‖ ≤ ‖u x‖ := by
          simpa using (cutPrimitive_lipschitz n).norm_sub_le (u x) 0
        calc
          ‖cutPrimitive n (u x)-max (u x) 0‖ ≤ ‖cutPrimitive n (u x)‖ + ‖max (u x) 0‖ := norm_sub_le _ _
          _ ≤ 2*‖u x‖ := by linarith [norm_positivePart (u x)]
          _ = ‖((2 : ℝ) • fun y => ‖u y‖) x‖ := by simp
    · exact Filter.Eventually.of_forall fun x => by
        simpa using (cutPrimitive_tendsto (u x)).sub_const (max (u x) 0)
  · have ht := bounded_smul_tendsto
      (fun n => (cutSlope_continuous n).comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
      (step_memLp_top hu.1.1.aestronglyMeasurable).aestronglyMeasurable
      hu.1.2.1 (by norm_num : (0 : ℝ) ≤ 1)
      (fun n => Filter.Eventually.of_forall fun x => cutSlope_norm_le n (u x))
      (Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num)
      (Filter.Eventually.of_forall fun x => cutSlope_tendsto (u x))
    simp only [sub_smul] at ht
    convert! ht using 1

end Bernoulli.SobolevCalculus

open scoped Manifold
namespace Bernoulli
open scoped _root_.Bernoulli
lemma exists_cutoff {d : ℕ} {K D : Set (Space d)} (hK : IsCompact K)
    (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ φ : Space d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D ∧
      (∀ᶠ x in 𝓝ˢ K, φ x = 1) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_thickening_subset_open hD hKD
  have hki : K ⊆ interior (Metric.cthickening (δ/2) K) := by
    exact (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ, hφ1, hφ0, hφb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Space d)) (n := ⊤) hK.isClosed hki
  refine ⟨φ, φ.contMDiff.contDiff, HasCompactSupport.intro (hK.cthickening) hφ0, ?_, hφ1, hφb⟩
  have hs : tsupport (φ : Space d → ℝ) ⊆ Metric.cthickening (δ/2) K := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)
end Bernoulli

namespace Bernoulli
open scoped _root_.Bernoulli
lemma H1.neg {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) : H1 D (fun x => -u x) (fun x => -G x) := by
  simpa using hu.const_smul (-1)
end Bernoulli

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma h1_positivePart (hD : IsOpen D) (hu : H1 D u G) :
    H1 D (fun x => max (u x) 0)
      (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x) := by
  have hum : MemLp (fun x => max (u x) 0) 2 (volume.restrict D) := by
    apply hu.1.mono ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      hu.1.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => norm_positivePart (u x)
  refine ⟨hum, (step_memLp_top hu.1.aestronglyMeasurable).smul hu.2.1, ?_⟩
  intro φ hφ h
  obtain ⟨χ, hχd, hχc, hχs, hχ1, _⟩ := exists_cutoff hφ.2.1.isCompact hD hφ.2.2
  have hχ : Test D χ := ⟨hχd, hχc, hχs⟩
  have hh := h10_positivePart hD (SobolevDensity.h10_mul_test hu hD hχ)
  have hc1 (x) (hx : x ∈ tsupport φ) : χ x = 1 := hχ1.self_of_nhdsSet x hx
  have hcG (x) (hx : x ∈ tsupport φ) : gradient χ x = 0 := by
    have heq : χ =ᶠ[𝓝 x] fun _ => 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    rw [heq.gradient_eq]
    exact gradient_const x 1
  have hφK : Test (tsupport φ) φ := ⟨hφ.1, hφ.2.1, subset_rfl⟩
  calc
    _ = ∫ x in D, max (χ x*u x) 0 * (fderiv ℝ φ x) h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport φ
        · rw [hc1 x hx, one_mul]
        · rw [hφK.fderiv_eq_zero_outside hx]
          simp
    _ = -(∫ x in D, inner ℝ ((if 0 < χ x*u x then (1 : ℝ) else 0) •
        (χ x • G x + u x • gradient χ x)) h * φ x) := hh.1.2.2 φ hφ h
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport φ
        · rw [hc1 x hx, hcG x hx]
          simp
        · rw [hφK.eq_zero_outside hx]
          simp

/-- A compactly supported H¹ function in the open set has zero trace. No
support or regularity condition is imposed on its given weak gradient. -/
lemma h10_of_local_compact_support (hD : IsOpen D) (hu : H1 D u G)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ D) : H10 D u G := by
  obtain ⟨χ, hχd, hχc, hχs, hχ1, _⟩ := exists_cutoff hc.isCompact hD hs
  have heq : (fun x => χ x*u x) = u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · rw [hχ1.self_of_nhdsSet x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hh := SobolevDensity.h10_mul_test hu hD ⟨hχd, hχc, hχs⟩
  rw [heq] at hh
  have hgrad := H1.gradient_unique hD hh.1 hu
  exact hh.congr (Filter.EventuallyEq.refl _ _) hgrad

/-- Stampacchia's zero-level-set property, obtained from the two truncations
and distributional uniqueness. -/
lemma gradient_zero_on_zero_set (hD : IsOpen D) (hu : H1 D u G) :
    ∀ᵐ x ∂volume.restrict D, u x = 0 → G x = 0 := by
  have hp := h1_positivePart hD hu
  have hn := h1_positivePart hD hu.neg
  have hh := hp.sub hn
  have heq : (fun x => max (u x) 0 - max (-u x) 0) = u := by
    funext x
    exact max_zero_sub_max_neg_zero_eq_self (u x)
  change H1 D (fun x => max (u x) 0 - max (-u x) 0) _ at hh
  rw [heq] at hh
  have hg := H1.gradient_unique hD hu hh
  filter_upwards [hg] with x hx hzero
  simpa [hzero] using hx

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
section Products
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_smul_strong_of_fixed {a : ℕ → α → ℝ} {b : α → ℝ}
    {V : ℕ → α → E} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (_hb : AEStronglyMeasurable b μ)
    (hV : ∀ n, MemLp (V n) 2 μ) (hG : MemLp G 2 μ)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hres : Tendsto (fun n => eLpNorm (fun x => (a n x-b x) • G x) 2 μ) atTop (𝓝 0))
    (hVG : Tendsto (fun n => eLpNorm (V n - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x • V n x - b x • G x) 2 μ)
      atTop (𝓝 0) := by
  have hfst := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hVG (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hfst
  have hsum := hfst.add hres
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  have heq : (fun x => a n x • V n x - b x • G x) =
      (fun x => a n x • (V n x-G x)) + (fun x => (a n x-b x) • G x) := by
    funext x
    simp only [Pi.add_apply, smul_sub, sub_smul]
    abel
  dsimp only
  rw [heq]
  apply (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
  apply add_le_add _ le_rfl
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun x => a n x • (V n x - G x)) (g := fun x => V n x - G x)
    ((ha n).smul ((hV n).sub hG).aestronglyMeasurable) ?_ 2
  filter_upwards [hab n] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (V n x - G x))

end Products
variable {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ} {G V : Space d → Space d}

lemma positivePart_gradient_strong_of_ae (hD : IsOpen D) (hu : H1 D u G)
    {f : ℕ → Space d → ℝ} {F : ℕ → Space d → Space d}
    (hf : ∀ n, H1 D (f n) (F n))
    (hpoint : ∀ᵐ x ∂volume.restrict D, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hFG : Tendsto (fun n => eLpNorm (F n - G) 2 (volume.restrict D)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < f n x then (1 : ℝ) else 0) • F n x -
      (if 0 < u x then (1 : ℝ) else 0) • G x) 2 (volume.restrict D)) atTop (𝓝 0) := by
  have hfp (n : ℕ) := step_memLp_top (hf n).1.aestronglyMeasurable
  have hup := step_memLp_top hu.1.aestronglyMeasurable
  apply bounded_smul_strong_of_fixed
    (fun n => (hfp n).aestronglyMeasurable) hup.aestronglyMeasurable
    (fun n => (hf n).2.1) hu.2.1
    (C := 1) (fun _ => Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num) ?_ hFG
  apply tendsto_eLpNorm_zero_of_dominated
    (f := fun n x => ((if 0 < f n x then (1 : ℝ) else 0) -
      (if 0 < u x then (1 : ℝ) else 0)) • G x)
    (fun n => ((hfp n).aestronglyMeasurable.sub hup.aestronglyMeasurable).smul
      hu.2.1.aestronglyMeasurable) (hu.2.1.norm.const_smul (2 : ℝ))
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      have hb : ‖(if 0 < f n x then (1 : ℝ) else 0) -
          (if 0 < u x then (1 : ℝ) else 0)‖ ≤ 2 := by split_ifs <;> norm_num
      simpa only [norm_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (norm_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        mul_le_mul_of_nonneg_right hb (norm_nonneg (G x))
  · filter_upwards [hpoint, gradient_zero_on_zero_set hD hu] with x hx hz
    by_cases hzero : u x = 0
    · simp only [hz hzero, smul_zero]
      exact tendsto_const_nhds
    · by_cases hpos : 0 < u x
      · apply tendsto_const_nhds.congr'
        filter_upwards [hx.eventually_const_lt hpos] with n hn
        simp [hpos, hn]
      · have hneg : u x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
        apply tendsto_const_nhds.congr'
        filter_upwards [hx.eventually_lt_const hneg] with n hn
        simp [hpos, not_lt.mpr hn.le]

lemma lipschitzWith_positivePart : LipschitzWith 1 (fun t : ℝ => max t 0) := by
  exact LipschitzWith.id.max_const 0

lemma h10_positivePart_add_test (hD : IsOpen D) (hu : H1 D u G)
    (hn : ∀ x, 0 ≤ u x) {φ : Space d → ℝ} (hφ : Test D φ) :
    H10 D (fun x => max (u x + φ x) 0 - u x)
      (fun x => (if 0 < u x + φ x then (1 : ℝ) else 0) •
        (G x + gradient φ x) - G x) := by
  have hh := (h1_positivePart hD (hu.add hφ.h1)).sub hu
  have hs : tsupport (fun x => max (u x + φ x) 0 - u x) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hnφ
    have hz := image_eq_zero_of_notMem_tsupport hnφ
    exact hx (by simp [hz, max_eq_left (hn x)])
  exact h10_of_local_compact_support hD hh
    (hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hφ.2.2)

lemma h10_positivePart_trace_pointwise (hD : IsOpen D)
    (hu : H1 D u G) (hn : ∀ x, 0 ≤ u x) (hv : H1 D v V)
    (hvu : H10 D (fun x => v x - u x) (fun x => V x - G x)) :
    H10 D (fun x => max (v x) 0 - u x)
      (fun x => (if 0 < v x then (1 : ℝ) else 0) • V x - G x) := by
  obtain ⟨φ, hφ, hφu, hφG⟩ := H10_sequence hvu
  let f : ℕ → Space d → ℝ := fun n x => u x + φ n x
  let F : ℕ → Space d → Space d := fun n x => G x + gradient (φ n) x
  have hf (n : ℕ) : H1 D (f n) (F n) := hu.add (hφ n).h1
  have hfv : Tendsto (fun n => eLpNorm (f n - v) 2 (volume.restrict D)) atTop (𝓝 0) := by
    convert! hφu using 1
    funext n
    congr 1
    funext x
    dsimp [f]
    ring
  have hFV : Tendsto (fun n => eLpNorm (F n - V) 2 (volume.restrict D)) atTop (𝓝 0) := by
    convert! hφG using 1
    funext n
    congr 1
    funext x
    dsimp [F]
    abel
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) hfv).exists_seq_tendsto_ae
  have htarget := (h1_positivePart hD hv).sub hu
  apply h10_of_strong htarget.1 htarget.2.1
    (fun n => h10_positivePart_add_test hD hu hn (hφ (ns n)))
  · have ht := lipschitz_tendsto_eLpNorm_of_aestronglyMeasurable lipschitzWith_positivePart
      (fun n => (hf (ns n)).1.aestronglyMeasurable) hv.1.aestronglyMeasurable
      (hfv.comp hns.tendsto_atTop)
    convert! ht using 1
    funext n
    congr 1
    funext x
    dsimp [f]
    ring
  · have ht := positivePart_gradient_strong_of_ae hD hv (fun n => hf (ns n))
      hpoint (hFV.comp hns.tendsto_atTop)
    convert! ht using 1
    funext n
    congr 1
    funext x
    dsimp [f, F]
    abel

lemma h10_positivePart_trace (hD : IsOpen D) (hu : H1 D u G)
    (hn : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x) (hv : H1 D v V)
    (hvu : H10 D (fun x => v x - u x) (fun x => V x - G x)) :
    H10 D (fun x => max (v x) 0 - u x)
      (fun x => (if 0 < v x then (1 : ℝ) else 0) • V x - G x) := by
  have heq : u =ᵐ[volume.restrict D] (fun x => max (u x) 0) := by
    filter_upwards [hn] with x hx
    exact (max_eq_left hx).symm
  have hh := h10_positivePart_trace_pointwise hD
    (hu.congr heq (Filter.EventuallyEq.refl _ _)) (fun x => le_max_right (u x) 0) hv
    (hvu.congr ((Filter.EventuallyEq.refl _ v).sub heq) (Filter.EventuallyEq.refl _ _))
  exact hh.congr ((Filter.EventuallyEq.refl _ (fun x => max (v x) 0)).sub heq.symm)
    (Filter.EventuallyEq.refl _ _)

end Bernoulli.SobolevCalculus

end
end
end

end OAI
