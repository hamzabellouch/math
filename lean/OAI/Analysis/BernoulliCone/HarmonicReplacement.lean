import OAI.Analysis.BernoulliCone.UpperLipschitzComparison

namespace OAI

universe uα uE

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ} {G V : Space d → Space d}

lemma energy_positivePart_le [IsFiniteMeasure (volume.restrict D)]
    (hv : MemLp v 2 (volume.restrict D)) (hV : MemLp V 2 (volume.restrict D)) :
    energy D (fun x => max (v x) 0)
      (fun x => (if 0 < v x then (1 : ℝ) else 0) • V x) ≤ energy D v V := by
  have hvm := lipschitzWith_positivePart.comp_memLp (by simp) hv
  have hVm : MemLp (fun x => (if 0 < v x then (1 : ℝ) else 0) • V x) 2 (volume.restrict D) :=
    (step_memLp_top hv.aestronglyMeasurable).smul hV
  apply integral_mono_ae
    ((hVm.integrable_norm_pow (by norm_num)).add (integrable_phase hvm.aestronglyMeasurable))
    ((hV.integrable_norm_pow (by norm_num)).add (integrable_phase hv.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : 0 < v x
    · simp [hx]
    · simp [hx]

/-- Full comparison with arbitrary signed Sobolev competitors follows from
precisely the nonnegative-competitor convention of the paper. -/
lemma compare_signed [IsFiniteMeasure (volume.restrict D)] (hD : IsOpen D)
    (hu : H1 D u G) (hn : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x)
    (hmin : ∀ (v : Space d → ℝ) (V : Space d → Space d),
      H1 D v V → (∀ᵐ x ∂volume.restrict D, 0 ≤ v x) →
      H10 D (fun x => v x - u x) (fun x => V x - G x) →
      energy D u G ≤ energy D v V)
    (hv : H1 D v V) (hvu : H10 D (fun x => v x-u x) (fun x => V x-G x)) :
    energy D u G ≤ energy D v V := by
  exact (hmin _ _ (h1_positivePart hD hv)
    (Filter.Eventually.of_forall fun x => le_max_right (v x) 0)
    (h10_positivePart_trace hD hu hn hv hvu)).trans (energy_positivePart_le hv.1 hv.2.1)

lemma energy_affine_le [IsFiniteMeasure (volume.restrict D)]
    {φ : Space d → ℝ} {W : Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D)) (hφ : MemLp φ 2 (volume.restrict D))
    (hG : MemLp G 2 (volume.restrict D)) (hW : MemLp W 2 (volume.restrict D)) (t : ℝ)
    (hphase : ∀ᵐ x ∂volume.restrict D, 0 < u x + t*φ x → 0 < u x) :
    energy D (fun x => u x+t*φ x) (fun x => G x+t • W x) ≤
      energy D u G + 2*t*(∫ x in D, inner ℝ (G x) (W x)) +
        t^2*(∫ x in D, ‖W x‖^2) := by
  have hG2 := hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hW2 := hW.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hGW := integrable_inner_of_memLp hG hW
  have hI := integrable_phase hu.aestronglyMeasurable
  have hF := (hG.add (hW.const_smul t)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hJ := integrable_phase (hu.add (hφ.const_smul t)).aestronglyMeasurable
  have hb : energy D (fun x => u x+t*φ x) (fun x => G x+t • W x) ≤
      ∫ x in D, ((‖G x‖^2 + (if 0 < u x then (1 : ℝ) else 0)) +
        (2*t)*inner ℝ (G x) (W x)) + t^2*‖W x‖^2 := by
    apply integral_mono_ae (hF.add hJ)
      (((hG2.add hI).add (hGW.const_mul (2*t))).add (hW2.const_mul (t^2)))
    filter_upwards [hphase] with x hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hi : (if 0 < u x+t*φ x then (1 : ℝ) else 0) ≤ if 0 < u x then 1 else 0 := by
      split_ifs with h1 h2 h3 <;> norm_num at *
      linarith [hx h1]
    linarith
  convert! hb using 1
  unfold energy
  have hs := integral_add ((hG2.add hI).add (hGW.const_mul (2*t))) (hW2.const_mul (t^2))
  have hs' := integral_add (hG2.add hI) (hGW.const_mul (2*t))
  simp only [Pi.add_apply] at hs hs'
  rw [hs, hs', integral_const_mul, integral_const_mul]

lemma linear_coefficient_nonpositive (A B : ℝ)
    (hq : ∀ t : ℝ, 0 < t → 0 ≤ -2*t*A+t^2*B) : A ≤ 0 := by
  by_contra hn
  have hA : 0 < A := lt_of_not_ge hn
  let t := A/(|B|+1)
  have ht : 0 < t := div_pos hA (by positivity)
  have hid : t*(|B|+1)= A := div_mul_cancel₀ A (by positivity)
  have hb : t*B < A := by
    have hl := mul_le_mul_of_nonneg_left (le_abs_self B) ht.le
    nlinarith
  have hc := mul_lt_mul_of_pos_left hb ht
  have hh := hq t ht
  nlinarith [mul_pos ht hA]

/-- Distributional subharmonicity follows without any continuity or
pointwise positivity assumption on the unknown minimizer. -/
lemma subharmonic_of_comparison [IsFiniteMeasure (volume.restrict D)] (hD : IsOpen D)
    (hu : H1 D u G) (hn : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x)
    (hmin : ∀ (v : Space d → ℝ) (V : Space d → Space d),
      H1 D v V → (∀ᵐ x ∂volume.restrict D, 0 ≤ v x) →
      H10 D (fun x => v x - u x) (fun x => V x - G x) →
      energy D u G ≤ energy D v V)
    {φ : Space d → ℝ} (hφ : Test D φ)
    (hφn : ∀ᵐ x ∂volume.restrict D, 0 ≤ φ x) :
    (∫ x in D, inner ℝ (G x) (gradient φ x)) ≤ 0 := by
  apply linear_coefficient_nonpositive _ (∫ x in D, ‖gradient φ x‖^2)
  intro t ht
  have hv := hu.add (hφ.h1.const_smul (-t))
  have hvu : H10 D (fun x => (u x + -t*φ x)-u x)
      (fun x => (G x + -t • gradient φ x)-G x) := by
    simpa only [add_sub_cancel_left] using hφ.h10_const_mul (-t)
  have hc := compare_signed hD hu hn hmin hv hvu
  have he := energy_affine_le hu.1 hφ.memLp hu.2.1 hφ.memLp_gradient (-t) (by
    filter_upwards [hφn] with x hx hp
    have := mul_nonneg ht.le hx
    linarith)
  have hh := hc.trans he
  nlinarith

end Bernoulli.SobolevCalculus

namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma LocalMinimizer.subharmonic {u : Space d → ℝ} (hu : LocalMinimizer D u) :
    ∃ G : Space d → Space d, H1Loc D u G ∧
      ∀ (c : Space d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ D →
      ∀ φ : Space d → ℝ, Test (Metric.ball c r) φ →
      (∀ᵐ x ∂volume.restrict (Metric.ball c r), 0 ≤ φ x) →
      (∫ x in Metric.ball c r, inner ℝ (G x) (gradient φ x)) ≤ 0 := by
  obtain ⟨hD, G, hG, hn, hmin⟩ := hu
  refine ⟨G, hG, fun c r hr hB φ hφ hφn => ?_⟩
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact SobolevCalculus.subharmonic_of_comparison Metric.isOpen_ball (hG c r hr hB)
    (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hB) hn)
    (hmin c r hr hB) hφ hφn

lemma LocalMinimizer.compare_signed {u : Space d → ℝ} (hu : LocalMinimizer D u) :
    ∃ G : Space d → Space d, H1Loc D u G ∧
      ∀ (c : Space d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ D →
      ∀ (v : Space d → ℝ) (V : Space d → Space d),
      H1 (Metric.ball c r) v V →
      H10 (Metric.ball c r) (fun x => v x-u x) (fun x => V x-G x) →
      energy (Metric.ball c r) u G ≤ energy (Metric.ball c r) v V := by
  obtain ⟨hD, G, hG, hn, hmin⟩ := hu
  refine ⟨G, hG, fun c r hr hB v V hv hvu => ?_⟩
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact SobolevCalculus.compare_signed Metric.isOpen_ball (hG c r hr hB)
    (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hB) hn)
    (hmin c r hr hB) hv hvu

end Bernoulli

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma gradient_norm_eq (f : Space d → ℝ) (x : Space d) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.norm_map _

lemma test_gradient_norm {f : Space d → ℝ} (hf : Test D f) (p : ℝ≥0∞) :
    eLpNorm (gradient f) p (volume.restrict D) = eLpNorm (fderiv ℝ f) p volume := by
  have hdf := (hf.1.continuous_fderiv (by simp)).aestronglyMeasurable (μ := volume)
  rw [eLpNorm_congr_norm_ae hf.memLp_gradient.aestronglyMeasurable hdf.restrict
    (Filter.Eventually.of_forall (gradient_norm_eq f))]
  exact eLpNorm_restrict_eq_of_support_subset hdf ((support_fderiv_subset ℝ).trans hf.2.2)

lemma test_poincare (hd : 2 ≤ d) (hD : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ f : Space d → ℝ, Test D f →
      eLpNorm f 2 (volume.restrict D) ≤ C * eLpNorm (gradient f) 2 (volume.restrict D) := by
  by_cases hd2 : d = 2
  · subst d
    let A := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space 2)) D 1 2
    let B : ℝ≥0 := (volume D).toNNReal ^ ((1 : ℝ) / 2)
    refine ⟨A * B, fun f hf => ?_⟩
    have hn := eLpNorm_le_eLpNorm_fderiv_of_le (volume : Measure (Space 2))
      (hf.1.of_le (by simp) : ContDiff ℝ 1 f) ((subset_tsupport f).trans hf.2.2)
      (p := 1) (q := 2) (by norm_num) (by simp) (by norm_num) hD
    have hm := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict D) (p := 1) (q := 2) (f := gradient f) (by norm_num)
      hf.memLp_gradient.aestronglyMeasurable
    have hB : (volume.restrict D) univ ^ ((1 : ℝ) / (1 : ℝ≥0∞).toReal -
        1 / (2 : ℝ≥0∞).toReal) = (B : ℝ≥0∞) := by
      dsimp [B]
      rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)]
      norm_num [ENNReal.coe_toNNReal hD.measure_lt_top.ne]
    rw [hB] at hm
    calc
      eLpNorm f 2 (volume.restrict D) = eLpNorm f 2 volume :=
        eLpNorm_restrict_eq_of_support_subset hf.1.continuous.aestronglyMeasurable
          ((subset_tsupport f).trans hf.2.2)
      _ ≤ A * eLpNorm (fderiv ℝ f) 1 volume := hn
      _ = A * eLpNorm (gradient f) 1 (volume.restrict D) := by rw [test_gradient_norm hf]
      _ ≤ A * (eLpNorm (gradient f) 2 (volume.restrict D) * B) := by gcongr
      _ = (A * B : ℝ≥0) * eLpNorm (gradient f) 2 (volume.restrict D) := by
        rw [ENNReal.coe_mul]; ring
  · refine ⟨eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space d)) D 2 2,
      fun f hf => ?_⟩
    have hn := eLpNorm_le_eLpNorm_fderiv (volume : Measure (Space d))
      (hf.1.of_le (by simp) : ContDiff ℝ 1 f) ((subset_tsupport f).trans hf.2.2)
      (p := 2) (by norm_num) (by simpa using (show (2 : ℕ) < d by omega)) hD
    rw [test_gradient_norm hf,
      eLpNorm_restrict_eq_of_support_subset hf.1.continuous.aestronglyMeasurable
        ((subset_tsupport f).trans hf.2.2)]
    exact hn

section LpContinuity
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

lemma tendsto_eLpNorm_of_strong {f : ℕ → α → E} {u : α → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 (eLpNorm u 2 μ)) := by
  have hLp : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub, Lp.enorm_toLp] using ht
  simpa only [Function.comp_def, Lp.enorm_toLp] using (continuous_enorm.tendsto _).comp hLp
end LpContinuity

/-- The Poincare inequality holds for arbitrary H1_0 competitors, not just
smooth or pointwise regular functions. -/
lemma h10_poincare (hd : 2 ≤ d) (hD : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ (u : Space d → ℝ) (G : Space d → Space d), H10 D u G →
      eLpNorm u 2 (volume.restrict D) ≤ C * eLpNorm G 2 (volume.restrict D) := by
  obtain ⟨C, hC⟩ := test_poincare hd hD
  refine ⟨C, fun u G hu => ?_⟩
  obtain ⟨f, hf, hfu, hfG⟩ := H10_sequence hu
  have h1 := tendsto_eLpNorm_of_strong (fun n => (hf n).memLp) hu.1.1 hfu
  have h2 := tendsto_eLpNorm_of_strong (fun n => (hf n).memLp_gradient) hu.1.2.1 hfG
  exact le_of_tendsto_of_tendsto h1
    (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.coe_ne_top))
    (Filter.Eventually.of_forall (fun n => hC (f n) (hf n)))
end Bernoulli.SobolevCalculus

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma Test.zero : Test D (fun _ => (0 : ℝ)) := by
  exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

lemma Test.add {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    Test D (f + g) := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩

lemma Test.gradient_add {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    gradient (f + g) = gradient f + gradient g := by
  funext x
  apply ext_inner_right ℝ
  intro h
  simp only [Pi.add_apply, inner_add_left, inner_gradient_left,
    fderiv_add (hf.1.differentiable (by simp) x) (hg.1.differentiable (by simp) x),
    add_apply]

lemma Test.sub {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    Test D (f - g) := by
  convert hf.add (hg.const_mul (-1)) using 1
  ext x
  simp [sub_eq_add_neg]

lemma Test.gradient_sub {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    gradient (f - g) = gradient f - gradient g := by
  funext x
  apply ext_inner_right ℝ
  intro h
  simp only [Pi.sub_apply, inner_sub_left, inner_gradient_left,
    fderiv_sub (hf.1.differentiable (by simp) x) (hg.1.differentiable (by simp) x),
    sub_apply]

lemma H10.const_smul {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H10 D u G) (t : ℝ) :
    H10 D (fun x => t * u x) (fun x => t • G x) := by
  obtain ⟨f, hf, hfu, hfG⟩ := SobolevCalculus.H10_sequence hu
  refine SobolevCalculus.h10_of_strong (hu.1.const_smul t).1 (hu.1.const_smul t).2.1
    (fun n => (hf n).h10_const_mul t) ?_ ?_
  · have heq (n : ℕ) : (fun x => t * f n x) - (fun x => t * u x) = t • (f n - u) := by
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hfu (a := ‖t‖ₑ) (Or.inr (by simp)))
  · have heq (n : ℕ) : (fun x => t • gradient (f n) x) - (fun x => t • G x) =
        t • (gradient (f n) - G) := by
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hfG (a := ‖t‖ₑ) (Or.inr (by simp)))

lemma H10.neg {u : Space d → ℝ} {G : Space d → Space d} (hu : H10 D u G) :
    H10 D (fun x => -u x) (fun x => -G x) := by
  simpa using hu.const_smul (-1)

namespace HarmonicReplacement

abbrev VectorLp (D : Set (Space d)) := Lp (Space d) 2 (volume.restrict D)
abbrev ScalarLp (D : Set (Space d)) := Lp ℝ 2 (volume.restrict D)

/-- Actual gradients of compactly supported smooth tests, in L2. -/
def testGradients (D : Set (Space d)) : Submodule ℝ (VectorLp D) where
  carrier := {F | ∃ (f : Space d → ℝ) (hf : Test D f),
    F = hf.memLp_gradient.toLp (gradient f)}
  zero_mem' := by
    refine ⟨fun _ => 0, Test.zero, ?_⟩
    simp [show gradient (fun _ : Space d => (0 : ℝ)) = 0 by funext x; exact gradient_const x 0]
  add_mem' := by
    rintro F V ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    simp only [hf.gradient_add hg]
    convert! (MemLp.toLp_add hf.memLp_gradient hg.memLp_gradient).symm
  smul_mem' := by
    rintro t F ⟨f, hf, rfl⟩
    refine ⟨fun x => t * f x, hf.const_mul t, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul t (hf.memLp_gradient.toLp (gradient f)),
      hf.memLp_gradient.coeFn_toLp, (hf.const_mul t).memLp_gradient.coeFn_toLp] with x h1 h2 h3
    simp only [Pi.smul_apply] at h1
    rw [h1, h2, h3, congrFun (hf.gradient_const_mul t) x]

/-- Closed gradient space used for Dirichlet harmonic replacement. -/
def zeroGradients (D : Set (Space d)) : Submodule ℝ (VectorLp D) :=
  (testGradients D).topologicalClosure

lemma h10_mem_zeroGradients {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H10 D u G) : hu.1.2.1.toLp G ∈ zeroGradients D := by
  obtain ⟨f, hf, hfu, hfG⟩ := SobolevCalculus.H10_sequence hu
  have hlim : Tendsto (fun n => (hf n).memLp_gradient.toLp (gradient (f n)))
      atTop (𝓝 (hu.1.2.1.toLp G)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub, Lp.enorm_toLp] using hfG
  exact (testGradients D).isClosed_topologicalClosure.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => subset_closure ⟨f n, hf n, rfl⟩)

lemma test_poincare_norm (hd : 2 ≤ d) (hD : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ (f : Space d → ℝ) (hf : Test D f),
      ‖hf.memLp.toLp f‖ ≤ C * ‖hf.memLp_gradient.toLp (gradient f)‖ := by
  obtain ⟨C, hC⟩ := SobolevCalculus.test_poincare hd hD
  refine ⟨C, fun f hf => ?_⟩
  have hn := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.memLp_gradient.ne)
    (hC f hf)
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal] using hn

lemma zeroGradients_h10 (hd : 2 ≤ d) (hD : Bornology.IsBounded D)
    {F : VectorLp D} (hF : F ∈ zeroGradients D) :
    ∃ u : ScalarLp D, H10 D u F := by
  obtain ⟨C, hC⟩ := test_poincare_norm hd hD
  obtain ⟨A, hA, ht⟩ := mem_closure_iff_seq_limit.mp hF
  choose f hf heq using hA
  let U : ℕ → ScalarLp D := fun n => (hf n).memLp.toLp (f n)
  let V : ℕ → VectorLp D := fun n => (hf n).memLp_gradient.toLp (gradient (f n))
  have htV : Tendsto V atTop (𝓝 F) := by
    have heq' : A = V := by funext n; exact heq n
    rwa [heq'] at ht
  have hdist (m n : ℕ) : dist (U m) (U n) ≤ C * dist (V m) (V n) := by
    dsimp [U, V]
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
    have hc := hC (f m - f n) ((hf m).sub (hf n))
    simpa only [(hf m).gradient_sub (hf n)] using hc
  have hUc : CauchySeq U := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp htV.cauchySeq (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => (hdist m n).trans_lt ?_⟩
    calc (C : ℝ) * dist (V m) (V n)
        ≤ (C + 1) * dist (V m) (V n) := by gcongr; linarith
      _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left (hN m hm n hn) (by positivity)
      _ = ε := by field_simp
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hUc
  refine ⟨u, SobolevCalculus.h10_of_strong (Lp.memLp u) (Lp.memLp F) (fun n => (hf n).h10) ?_ ?_⟩
  · have hu' : Tendsto U atTop (𝓝 ((Lp.memLp u).toLp u)) := by
      simpa only [Lp.toLp_coeFn] using hu
    have h := tendsto_iff_enorm_sub_tendsto_zero.mp hu'
    simpa only [U, ← MemLp.toLp_sub, Lp.enorm_toLp] using h
  · have hF' : Tendsto V atTop (𝓝 ((Lp.memLp F).toLp F)) := by
      simpa only [Lp.toLp_coeFn] using htV
    have h := tendsto_iff_enorm_sub_tendsto_zero.mp hF'
    simpa only [V, ← MemLp.toLp_sub, Lp.enorm_toLp] using h

theorem exists_replacement (hd : 2 ≤ d) (hD : Bornology.IsBounded D)
    {u : Space d → ℝ} {G : Space d → Space d} (hu : H1 D u G) :
    ∃ (h : Space d → ℝ) (H : Space d → Space d), H1 D h H ∧
      H10 D (h - u) (H - G) ∧
      ∀ (v : Space d → ℝ) (V : Space d → Space d), H10 D v V →
        (∫ x in D, inner ℝ (H x) (V x)) = 0 := by
  let K := zeroGradients D
  let : CompleteSpace K := (testGradients D).isClosed_topologicalClosure.completeSpace_coe
  let W : VectorLp D := K.starProjection (hu.2.1.toLp G)
  obtain ⟨w, hw⟩ := zeroGradients_h10 hd hD (K.starProjection_apply_mem (hu.2.1.toLp G))
  refine ⟨u - w, G - W, hu.sub hw.1, ?_, ?_⟩
  · convert hw.neg using 1 <;> ext x <;> simp only [Pi.sub_apply, W] <;> abel_nf
  · intro v V hv
    have ho := K.starProjection_inner_eq_zero (hu.2.1.toLp G) (hv.1.2.1.toLp V)
      (h10_mem_zeroGradients hv)
    rw [L2.inner_def] at ho
    calc
      (∫ x in D, inner ℝ ((G - W) x) (V x)) =
          ∫ x in D, inner ℝ ((hu.2.1.toLp G - W) x) (hv.1.2.1.toLp V x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (hu.2.1.toLp G) W, hu.2.1.coeFn_toLp,
          hv.1.2.1.coeFn_toLp] with x hs hG hV
        simp only [Pi.sub_apply] at hs ⊢
        rw [hs, hG, hV]
      _ = 0 := ho

lemma orthogonal_energy_identity {G H : Space d → Space d}
    (hG : MemLp G 2 (volume.restrict D)) (hH : MemLp H 2 (volume.restrict D))
    (ho : (∫ x in D, inner ℝ (H x) ((G - H) x)) = 0) :
    (∫ x in D, ‖(G - H) x‖^2) =
      (∫ x in D, ‖G x‖^2) - (∫ x in D, ‖H x‖^2) := by
  have hH2 := hH.integrable_norm_pow (by norm_num)
  have hW2 := (hG.sub hH).integrable_norm_pow (by norm_num)
  have hHW := integrable_inner_of_memLp hH (hG.sub hH)
  have heq : (∫ x in D, ‖G x‖^2) =
      ∫ x in D, (‖H x‖^2 + ‖(G - H) x‖^2) + 2 * inner ℝ (H x) ((G - H) x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have hn := norm_add_sq_real (H x) ((G - H) x)
      simp only [Pi.sub_apply, add_sub_cancel] at hn
      dsimp only [Pi.sub_apply]
      linarith only [hn]
  have hadd := integral_add (hH2.add hW2) (hHW.const_mul 2)
  have hadd' := integral_add hH2 hW2
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd', integral_const_mul, ho, mul_zero, add_zero] at heq
  linarith

/-- The Bernoulli term is retained in the harmonic-replacement estimate. -/
lemma replacement_energy_estimate [IsFiniteMeasure (volume.restrict D)]
    {u h : Space d → ℝ} {G H : Space d → Space d}
    (hu : H1 D u G) (hh : H1 D h H)
    (ht : H10 D (h-u) (H-G))
    (ho : ∀ v V, H10 D v V → (∫ x in D, inner ℝ (H x) (V x)) = 0)
    (hmin : energy D u G ≤ energy D h H) :
    (∫ x in D, ‖(G-H) x‖^2) +
      (∫ x in D, if 0 < u x then (1 : ℝ) else 0) ≤ (volume D).toReal := by
  have hn : H10 D (u-h) (G-H) := by
    convert ht.neg using 1 <;> ext x <;> simp only [Pi.sub_apply] <;> abel_nf
  have hid := orthogonal_energy_identity hu.2.1 hh.2.1 (ho _ _ hn)
  have he (f : Space d → ℝ) (F : Space d → Space d) (hf : H1 D f F) :
      energy D f F = (∫ x in D, ‖F x‖^2) +
        (∫ x in D, if 0 < f x then (1 : ℝ) else 0) := by
    unfold energy
    exact integral_add (hf.2.1.integrable_norm_pow (by norm_num))
      (integrable_phase hf.1.aestronglyMeasurable)
  have hp : (∫ x in D, if 0 < h x then (1 : ℝ) else 0) ≤ (volume D).toReal := by
    calc
      _ ≤ ∫ _x in D, (1 : ℝ) := integral_mono_ae
        (integrable_phase hh.1.aestronglyMeasurable) (integrable_const 1)
        (Filter.Eventually.of_forall fun x => by dsimp only; split_ifs <;> norm_num)
      _ = _ := by simp [Measure.real]
  rw [he u G hu, he h H hh] at hmin
  linarith

end HarmonicReplacement

/-- Actual Bernoulli minimizers admit harmonic replacements with the full
volume-term estimate, without a regularity assumption on the minimizer. -/
lemma LocalMinimizer.harmonic_replacement (hd : 2 ≤ d)
    {u : Space d → ℝ} (hu : LocalMinimizer D u) :
    ∃ G : Space d → Space d, H1Loc D u G ∧
      ∀ (c : Space d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ D →
      ∃ (h : Space d → ℝ) (H : Space d → Space d),
        H1 (Metric.ball c r) h H ∧ H10 (Metric.ball c r) (h-u) (H-G) ∧
        (∀ v V, H10 (Metric.ball c r) v V →
          (∫ x in Metric.ball c r, inner ℝ (H x) (V x)) = 0) ∧
        (∫ x in Metric.ball c r, ‖(G-H) x‖^2) +
          (∫ x in Metric.ball c r, if 0 < u x then (1 : ℝ) else 0) ≤
            (volume (Metric.ball c r)).toReal := by
  obtain ⟨G, hG, hc⟩ := hu.compare_signed
  refine ⟨G, hG, fun c r hr hB => ?_⟩
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨h, H, hh, ht, ho⟩ := HarmonicReplacement.exists_replacement hd
    Metric.isBounded_ball (hG c r hr hB)
  exact ⟨h, H, hh, ht, ho, HarmonicReplacement.replacement_energy_estimate
    (hG c r hr hB) hh ht ho (hc c r hr hB h H hh ht)⟩

end Bernoulli

end
end
end
end

end OAI
