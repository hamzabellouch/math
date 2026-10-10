import OAI.Geometry.Kahler.BaseLogJetBounds

namespace OAI

universe uKahler8561_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0:Base) 1)

@[simp] lemma sphere_norm (ξ : Sphere) : ‖(ξ:Base)‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp ξ.property

def Represents (μ : Measure Sphere) : Prop :=
  ∀ p : MvPolynomial (Fin 2) ℂ, (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p ∂μ) =
    MvPolynomial.eval (fun _ => 0) p

lemma base_eq_sum_single (z : Base) : z = ∑ i : Fin 2, z i • EuclideanSpace.single i 1 := by
  ext j
  fin_cases j <;> simp

lemma multilinear_diagonal_polynomial {n : ℕ} (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => Base) ℂ) :
    ∃ p : MvPolynomial (Fin 2) ℂ, ∀ z : Base,
      M (fun _ => z) = MvPolynomial.eval (fun i => z i) p := by
  classical
  refine ⟨∑ r : Fin n → Fin 2, MvPolynomial.C (M (fun i => EuclideanSpace.single (r i) 1)) *
    ∏ i : Fin n, MvPolynomial.X (r i), ?_⟩
  intro z
  calc
    M (fun _ => z) = M (fun _ => ∑ j : Fin 2, z j • EuclideanSpace.single j 1) := by
      congr 1
      funext i
      exact base_eq_sum_single z
    _ = ∑ r : Fin n → Fin 2, M (fun i => z (r i) • EuclideanSpace.single (r i) 1) :=
      M.toMultilinearMap.map_sum _
    _ = ∑ r : Fin n → Fin 2, (∏ i : Fin n, z (r i)) * M (fun i => EuclideanSpace.single (r i) 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact M.toMultilinearMap.map_smul_univ _ _
    _ = _ := by simp [map_sum,map_mul,map_prod,mul_comm]

lemma continuous_integrable {E : Type uKahler8561_1} [NormedAddCommGroup E] {μ : Measure Sphere}
    [IsFiniteMeasure μ] {f : Sphere → E} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma Represents.multilinear_moment {μ : Measure Sphere} (hμ : Represents μ) {n : ℕ}
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => Base) ℂ) :
    (∫ ξ : Sphere, M (fun _ => (ξ:Base)) ∂μ) = M (fun _ => 0) := by
  obtain ⟨p,hp⟩ := multilinear_diagonal_polynomial M
  simpa [hp] using hμ p

lemma Represents.partialSum_moment {μ : Measure Sphere} [IsFiniteMeasure μ] (hμ : Represents μ)
    (p : FormalMultilinearSeries ℂ Base ℂ) (n : ℕ) (c : ℂ) :
    (∫ ξ : Sphere, p.partialSum n (c • (ξ:Base)) ∂μ) = p.partialSum n 0 := by
  classical
  simp only [FormalMultilinearSeries.partialSum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have he : ∀ z : Base, p m (fun _ => c • z) = c^m * p m (fun _ => z) := by
      intro z
      simpa [smul_eq_mul] using (p m).toMultilinearMap.map_smul_univ (fun _ => c) (fun _ => z)
    simp_rw [he]
    rw [integral_const_mul,hμ.multilinear_moment]
    simpa using (he (0:Base)).symm
  · intro m hm
    apply continuous_integrable
    exact (p m).cont.comp (continuous_pi (fun _ => (continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c))

lemma Represents.local_analytic_mean {μ : Measure Sphere} [IsProbabilityMeasure μ]
    (hμ : Represents μ) {H : Base → ℂ} (hH : AnalyticAt ℂ H 0) :
    (fun c : ℂ => ∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) =ᶠ[𝓝 0] fun _ => H 0 := by
  obtain ⟨p,r,hp⟩ := hH
  obtain ⟨r',hr'0,hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  obtain ⟨a,ha,C,hC,hbound⟩ := hp.uniform_geometric_approx hr'r
  have hr' : 0 < (r':ℝ) := by exact_mod_cast hr'0
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr'] with c hc
  have hc' : ‖c‖ < r' := by simpa using hc
  have hm : ∀ n : ℕ, ‖(∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ)-H 0‖ ≤ C*a^(n+1) := by
    intro n
    have hint : Integrable (fun ξ : Sphere => H (c • (ξ:Base))) μ := by
      apply continuous_integrable
      apply hp.continuousOn.comp_continuous (f := fun ξ : Sphere => c • (ξ:Base))
        ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
      intro ξ
      rw [mem_eball_zero_iff]
      calc
        ‖c • (ξ:Base)‖ₑ = ↑(‖c‖₊) := by
          change ((‖c • (ξ:Base)‖₊:ℝ≥0∞)) = _
          congr 1
          apply NNReal.coe_injective
          simp [norm_smul]
        _ < ↑r' := by exact_mod_cast hc'
        _ < r := hr'r
    have hintp : Integrable (fun ξ : Sphere => p.partialSum (n+1) (c • (ξ:Base))) μ := by
      apply continuous_integrable
      exact (p.partialSum_continuous _).comp ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
    have hzero : p.partialSum (n+1) 0 = H 0 := by
      simp only [FormalMultilinearSeries.partialSum]
      rw [Finset.sum_eq_single 0]
      · exact hp.coeff_zero _
      · intro m hm hm0
        exact (p m).map_coord_zero ⟨0, Nat.pos_of_ne_zero hm0⟩ rfl
      · simp
    rw [← hzero, ← hμ.partialSum_moment p (n+1) c, ← integral_sub hint hintp]
    refine (norm_integral_le_of_norm_le_const (C := C*a^(n+1)) ?_).trans_eq (by simp)
    filter_upwards [] with ξ
    simpa using hbound (c • (ξ:Base)) (by simpa [norm_smul] using hc') (n+1)
  have hlim : Tendsto (fun n : ℕ => C*a^(n+1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2).comp (tendsto_add_atTop_nat 1))
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hm)) (norm_nonneg _)))

lemma radial_mem_ball {c : ℂ} (hc : ‖c‖ < 1) (ξ : Sphere) : c • (ξ:Base) ∈ ball := by
  simpa [ball,norm_smul] using hc

lemma radial_continuous {H : Base → ℂ} (hH : ContinuousOn H ball) {c : ℂ} (hc : ‖c‖ < 1) :
    Continuous (fun ξ : Sphere => H (c • (ξ:Base))) :=
  hH.comp_continuous
    ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
    (radial_mem_ball hc)

lemma analytic_radial_integral {μ : Measure Sphere} [IsFiniteMeasure μ]
    {H : Base → ℂ} (hH : AnalyticOnNhd ℂ H ball) :
    AnalyticOnNhd ℂ (fun c : ℂ => ∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro c hc
  have hc' : ‖c‖ < 1 := by simpa using hc
  obtain ⟨R,hcR,hR1⟩ := exists_between hc'
  have hR0 : 0 < R := (norm_nonneg _).trans_lt hcR
  have hsubset : Metric.closedBall (0:Base) R ⊆ ball := by
    intro z hz
    exact (show ‖z‖ ≤ R by simpa using hz).trans_lt hR1
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Base) R).bddAbove_image
    (hH.fderiv.continuousOn.norm.mono hsubset)
  let F' : ℂ → Sphere → ℂ := fun d ξ => fderiv ℂ H (d • (ξ:Base)) (ξ:Base)
  have hF' : ∀ d : ℂ, ‖d‖ < 1 → Continuous (F' d) := by
    intro d hd
    exact ((hH.fderiv.continuousOn.comp_continuous
      ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul d)
      (radial_mem_ball hd)).clm_apply continuous_subtype_val)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun d : ℂ => fun ξ : Sphere => H (d • (ξ:Base)))
    (F' := F') (bound := fun _ => C) (s := Metric.ball 0 R)
    (Metric.isOpen_ball.mem_nhds (by simpa using hcR))
    (?_) (continuous_integrable (radial_continuous hH.continuousOn hc'))
    ((hF' c hc').aestronglyMeasurable) (?_) (integrable_const C) (?_)
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [Metric.isOpen_ball.mem_nhds (show c ∈ Metric.ball (0:ℂ) R by simpa using hcR)] with d hd
    exact (radial_continuous hH.continuousOn
      ((show ‖d‖ < R by simpa using hd).trans hR1)).aestronglyMeasurable
  · filter_upwards [] with ξ d hd
    have hdR : ‖d‖ < R := by simpa using hd
    calc
      ‖F' d ξ‖ ≤ ‖fderiv ℂ H (d • (ξ:Base))‖ * ‖(ξ:Base)‖ := (fderiv ℂ H _).le_opNorm _
      _ = ‖fderiv ℂ H (d • (ξ:Base))‖ := by simp
      _ ≤ C := hC (mem_image_of_mem _ (by simpa [norm_smul] using hdR.le))
  · filter_upwards [] with ξ d hd
    have ha := (hH (d • (ξ:Base)) (radial_mem_ball
      ((show ‖d‖ < R by simpa using hd).trans hR1) ξ)).differentiableAt
    convert ha.hasFDerivAt.comp_hasDerivAt d ((hasDerivAt_id d).smul_const (ξ:Base)) using 1 <;> simp [F',Function.comp_def]

lemma Represents.analytic_mean {μ : Measure Sphere} [IsProbabilityMeasure μ]
    (hμ : Represents μ) {H : Base → ℂ} (hH : AnalyticOnNhd ℂ H ball) {c : ℂ} (hc : ‖c‖ < 1) :
    (∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) = H 0 := by
  have he := (analytic_radial_integral hH).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const (v := H 0)) (convex_ball (0:ℂ) 1).isPreconnected
    (show (0:ℂ) ∈ Metric.ball 0 1 by simp)
    (hμ.local_analytic_mean (hH 0 (by simp [ball])))
  exact he (by simpa using hc)

theorem representing_mean_criterion {u : Base → ℝ} (hu : ContinuousOn u ball)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < 1)
    (μ : ℕ → Measure Sphere) [∀ n, IsProbabilityMeasure (μ n)] (hμ : ∀ n, Represents (μ n))
    (hmean : Tendsto (fun n => ∫ ξ : Sphere, u ((r n:ℂ) • (ξ:Base)) ∂μ n) atTop atBot) :
    ¬ ∃ (H : Base → ℂ) (C : ℝ), AnalyticOnNhd ℂ H ball ∧
      ∀ z ∈ ball, (H z).re ≤ C + u z := by
  rintro ⟨H,C,hH,hminor⟩
  have hb : ∀ n, (H 0).re ≤ C + ∫ ξ : Sphere, u ((r n:ℂ) • (ξ:Base)) ∂μ n := by
    intro n
    have hn : ‖(r n:ℂ)‖ < 1 := by simpa [abs_of_pos (hr n).1] using (hr n).2
    have hiH := continuous_integrable (μ := μ n) (radial_continuous hH.continuousOn hn)
    have hiu : Integrable (fun ξ : Sphere => u ((r n:ℂ) • (ξ:Base))) (μ n) := by
      apply continuous_integrable
      exact hu.comp_continuous
        ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul (r n:ℂ))
        (radial_mem_ball hn)
    have hle := integral_mono (hiH.re) ((integrable_const C).add hiu)
      (fun ξ => hminor _ (radial_mem_ball hn ξ))
    change (∫ ξ : Sphere, (H ((r n:ℂ) • (ξ:Base))).re ∂μ n) ≤
      ∫ ξ : Sphere, C + u ((r n:ℂ) • (ξ:Base)) ∂μ n at hle
    rw [integral_add (integrable_const C) hiu] at hle
    have he := Complex.reCLM.integral_comp_comm hiH
    change (∫ ξ : Sphere, (H ((r n:ℂ) • (ξ:Base))).re ∂μ n) =
      (∫ ξ : Sphere, H ((r n:ℂ) • (ξ:Base)) ∂μ n).re at he
    rw [he, (hμ n).analytic_mean hH hn] at hle
    simpa using hle
  have hn := hmean.eventually (eventually_lt_atBot ((H 0).re-C-1))
  obtain ⟨n,hn⟩ := hn.exists
  have := hb n
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
