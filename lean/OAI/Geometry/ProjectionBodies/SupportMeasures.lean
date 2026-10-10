import OAI.Geometry.ProjectionBodies.Homothety

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma gauge_pos_sphere {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (u : Sphere n) : 0 < gauge K (u : Space n) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  have hw : wulff s = K := wulff_support hK hc ⟨0,mem_of_mem_nhds h0⟩
  rw [← hw,gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

def gaugeDensity {n : ℕ} (K : Set (Space n)) (u : Sphere n) : ENNReal :=
  ENNReal.ofReal ((gauge K (u : Space n))⁻¹^n)

def gaugeProjectionMeasure {n : ℕ} (K : Set (Space n)) : Measure (Space n) :=
  Measure.map (fun u : Sphere n => ∇ (gauge K) (u : Space n))
    ((sigma n).withDensity (gaugeDensity K))

lemma gaugeDensity_measurable {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) : Measurable (gaugeDensity K) :=
  ENNReal.measurable_ofReal.comp ((((continuous_gauge hc h0).measurable.comp
    measurable_subtype_coe).inv).pow_const n)

lemma gaugeDensity_toReal {n : ℕ} (K : Set (Space n)) (u : Sphere n) :
    (gaugeDensity K u).toReal=(gauge K (u : Space n))⁻¹^n := by
  exact ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (gauge_nonneg _)) _)

lemma gaugeMeasure_integral {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) {f : Space n → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ x,f x ∂gaugeProjectionMeasure K =
      mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*f (∇ (gauge K) (u : Space n))) := by
  have hm : Measurable (fun u : Sphere n => ∇ (gauge K) (u : Space n)) :=
    (measurable_gradient _).comp measurable_subtype_coe
  rw [gaugeProjectionMeasure,integral_map_of_stronglyMeasurable hm hf,
    integral_withDensity_eq_integral_toReal_smul (gaugeDensity_measurable hc h0)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [gaugeDensity_toReal,smul_eq_mul,mean]

lemma gaugeMeasure_finite {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    IsFiniteMeasure (gaugeProjectionMeasure K) := by
  have hp := gauge_pos_sphere hK hc h0
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hi := hcont.integrable_of_hasCompactSupport (μ := sigma n) (HasCompactSupport.of_compactSpace _)
  have hf : ∫⁻ u, gaugeDensity K u ∂sigma n ≠ ⊤ := by
    unfold gaugeDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun u => (pow_nonneg (inv_nonneg.mpr (hp u).le) n)))]
    exact ENNReal.ofReal_ne_top
  have := isFiniteMeasure_withDensity hf
  exact Measure.isFiniteMeasure_map _ _

lemma gaugeMeasure_mass {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    (gaugeProjectionMeasure K).real univ=volume.real K/kappa n := by
  have hi := gaugeMeasure_integral hc h0 (f := fun _ => 1) stronglyMeasurable_const
  simp only [integral_const,smul_eq_mul,mul_one] at hi
  rw [hi,gauge_volume hc h0 (gauge_pos_sphere hK hc h0)]
  field_simp [(kappa_pos n).ne']

lemma gaugeMeasure_probability {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hv : volume.real K=kappa n) : IsProbabilityMeasure (gaugeProjectionMeasure K) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [show (gaugeProjectionMeasure K univ).toReal=(gaugeProjectionMeasure K).real univ from rfl,
    gaugeMeasure_mass hK hc h0,hv,div_self (kappa_pos n).ne']

lemma gaugeMeasure_bounded {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂gaugeProjectionMeasure K, ‖x‖ ≤ B := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  refine ⟨C,C.coe_nonneg,?_⟩
  have hm : Measurable (fun u : Sphere n => ∇ (gauge K) (u : Space n)) :=
    (measurable_gradient _).comp measurable_subtype_coe
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  apply Eventually.of_forall
  intro u
  have he : ‖∇ (gauge K) (u : Space n)‖=‖fderiv ℝ (gauge K) (u : Space n)‖ :=
    (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map _
  rw [he]
  exact norm_fderiv_le_of_lipschitz ℝ hC

lemma boundedMeasure_integrable_continuous {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hb : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂μ, ‖x‖ ≤ B) {f : Space n → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,_,hB⟩ := hb
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space n) B).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hB] with x hx
  exact hC x (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma gaugeMeasure_shadow {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) :
    2*shadowVolume K u=n*kappa n*∫ x,|⟪x,(u : Space n)⟫| ∂gaugeProjectionMeasure K := by
  rw [gaugeMeasure_integral hc h0 (by fun_prop)]
  exact shadow_gauge_formula hK hc h0 u

lemma gaugeMeasure_firstVariation {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*∫ x,support M x ∂gaugeProjectionMeasure K) (Ici 0) 0 := by
  rw [gaugeMeasure_integral hcK h0 (support_continuous hM).stronglyMeasurable]
  exact minkowski_volume_derivative hK hcK h0 hM hcM hMn

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

def supportFunctional {n : ℕ} (μ : Measure (Space n)) (K : Set (Space n)) : ℝ :=
  ∫ x,support K x ∂μ

def normalizedVolume {n : ℕ} (K : Set (Space n)) : ℝ :=
  volumeRoot K/(kappa n)^((n:ℝ)⁻¹)

lemma normalizedVolume_formula {n : ℕ} (K : Set (Space n)) :
    normalizedVolume K=(volume.real K/kappa n)^((n:ℝ)⁻¹) := by
  rw [Real.div_rpow measureReal_nonneg (kappa_pos n).le]
  rfl

lemma gaugeMeasure_functional {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (hv : volume.real K=kappa n)
    (hM : IsCompact M) (hcM : Convex ℝ M) (hiM : (interior M).Nonempty) :
    normalizedVolume M ≤ supportFunctional (gaugeProjectionMeasure K) M ∧
      (supportFunctional (gaugeProjectionMeasure K) M=normalizedVolume M →
        ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M) := by
  have hiK : (interior K).Nonempty := ⟨0,mem_interior_iff_mem_nhds.mpr h0⟩
  have hV := gaugeMeasure_firstVariation hK hcK h0 hM hcM (hiM.mono interior_subset)
  obtain ⟨hlow,heq⟩ := minkowski_derivative_bound_equality hn hK hcK hiK hM hcM hiM hV
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hp : 0 < (kappa n)^((n:ℝ)⁻¹) := Real.rpow_pos_of_pos (kappa_pos n) _
  have hroot : volumeRoot K=(kappa n)^((n:ℝ)⁻¹) := by unfold volumeRoot; rw [hv]
  have hmul : n*kappa n*normalizedVolume M=(n:ℝ)*volumeRoot K^(n-1)*volumeRoot M := by
    have hpow := volumeRoot_pow (show 0<n by omega) K
    have hsplit : volumeRoot K^(n-1)*volumeRoot K=kappa n := by
      rw [← pow_succ,Nat.sub_add_cancel (by omega),hpow,hv]
    rw [normalizedVolume,← hroot,← hsplit]
    field_simp [(volumeRoot_pos hK hiK).ne']
  refine ⟨?_,fun h => heq ?_⟩
  · rw [← hmul] at hlow
    exact (mul_le_mul_iff_right₀ (mul_pos hnR (kappa_pos n))).mp hlow
  · change n*kappa n*supportFunctional (gaugeProjectionMeasure K) M=_
    rw [h,hmul]

lemma gaugeMeasure_self {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    supportFunctional (gaugeProjectionMeasure K) K=volume.real K/kappa n := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  have hV := gaugeMeasure_firstVariation hK hc h0 hK hc hKn
  have hd : HasDerivAt (fun t : ℝ => (1+t)^n*volume.real K) (n*volume.real K) 0 := by
    simpa only [id_eq,Pi.pow_apply,add_zero,one_pow,mul_one] using
      (((hasDerivAt_id (0:ℝ)).const_add 1).pow n).mul_const (volume.real K)
  have he (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      volume.real (K+t • K)=(1+t)^n*volume.real K := by
    have he : K+t • K=(1+t) • K := by simpa only [one_smul] using (hc.add_smul (by norm_num : (0:ℝ)≤1) ht).symm
    rw [he,volumeReal_smul_nonneg (by have := ht; change 0 ≤ t at this; linarith : 0≤1+t)]
    simp only [finrank_euclideanSpace_fin]
  have hd' := hd.hasDerivWithinAt (s := Ici (0:ℝ)) |>.congr he (he 0 (by norm_num))
  have hdEq := (hV.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hd'.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))
  change n*kappa n*supportFunctional (gaugeProjectionMeasure K) K=n*volume.real K at hdEq
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  apply (eq_div_iff (kappa_pos n).ne').mpr
  rw [mul_assoc] at hdEq
  simpa only [mul_comm] using (mul_left_cancel₀ hn hdEq)

lemma shadowVolume_pos {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Space n) : 0 < shadowVolume K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hball : ball (0 : perpendicular u) r ⊆ (perpendicular u).orthogonalProjectionOnto '' K := by
    intro z hz
    refine ⟨z,hrK ?_,?_⟩
    · simpa only [mem_ball,dist_zero_right,Submodule.norm_coe] using hz
    · exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
  have hpos : 0 < (volume : Measure (perpendicular u))
      ((perpendicular u).orthogonalProjectionOnto '' K) :=
    (measure_ball_pos volume 0 hr).trans_le (measure_mono hball)
  exact ENNReal.toReal_pos hpos.ne'
    (hK.image (perpendicular u).orthogonalProjectionOnto.continuous).measure_ne_top

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma convex_deriv_limit {ι : Type uι} {l : Filter ι} {f : ι → ℝ → ℝ}
    {g : ℝ → ℝ} {d : ι → ℝ} {a : ℝ}
    (hf : ∀ j, ConvexOn ℝ univ (f j))
    (hd : ∀ j, HasDerivAt (f j) (d j) 0)
    (hg : HasDerivAt g a 0)
    (hlim : ∀ t, Tendsto (fun j => f j t) l (𝓝 (g t))) :
    Tendsto d l (𝓝 a) := by
  have hs (t : ℝ) : Tendsto (fun j => slope (f j) 0 t) l (𝓝 (slope g 0 t)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul] using
      ((hlim t).sub (hlim 0)).const_mul (t - 0)⁻¹
  rw [tendsto_order]
  constructor
  · intro b hb
    have hh : ∀ᶠ t in 𝓝[<] (0 : ℝ), b < slope g 0 t :=
      (hg.tendsto_slope.mono_left (nhdsWithin_mono _ (by grind : Iio (0 : ℝ) ⊆ {0}ᶜ))).eventually
        (eventually_gt_nhds hb)
    have ht : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
    obtain ⟨t, ht, hbt⟩ := (ht.and hh).exists
    filter_upwards [(hs t).eventually (eventually_gt_nhds hbt)] with j hj
    have hj' := (hf j).slope_le_of_hasDerivAt (mem_univ t) (mem_univ 0) ht (hd j)
    rw [slope_comm] at hj'
    exact hj.trans_le hj'
  · intro b hb
    have hh : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t < b :=
      (hg.tendsto_slope.mono_left (nhdsWithin_mono _ (by grind : Ioi (0 : ℝ) ⊆ {0}ᶜ))).eventually
        (eventually_lt_nhds hb)
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, hbt⟩ := (ht.and hh).exists
    filter_upwards [(hs t).eventually (eventually_lt_nhds hbt)] with j hj
    exact ((hf j).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ t) ht (hd j)).trans_lt hj

lemma convex_fderiv_apply_limit {n : ℕ} {ι : Type uι} {l : Filter ι}
    {f : ι → Space n → ℝ} {g : Space n → ℝ} {x : Space n}
    (hf : ∀ j, ConvexOn ℝ univ (f j)) (hd : ∀ j, DifferentiableAt ℝ (f j) x)
    (hg : DifferentiableAt ℝ g x)
    (hlim : ∀ y, Tendsto (fun j => f j y) l (𝓝 (g y))) (w : Space n) :
    Tendsto (fun j => fderiv ℝ (f j) x w) l (𝓝 (fderiv ℝ g x w)) := by
  apply convex_deriv_limit (fun j => line_convex (hf j) x w)
  · intro j
    have h : HasFDerivAt (f j) (fderiv ℝ (f j) x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hd j).hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x w 0)
  · have h : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using hg.hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x w 0)
  · intro t
    exact hlim (x + t • w)

lemma convex_gradient_limit {n : ℕ} {ι : Type uι} {l : Filter ι}
    {f : ι → Space n → ℝ} {g : Space n → ℝ} {x : Space n}
    (hf : ∀ j, ConvexOn ℝ univ (f j)) (hd : ∀ j, DifferentiableAt ℝ (f j) x)
    (hg : DifferentiableAt ℝ g x)
    (hlim : ∀ y, Tendsto (fun j => f j y) l (𝓝 (g y))) :
    Tendsto (fun j => ∇ (f j) x) l (𝓝 (∇ g x)) := by
  have hp : Tendsto (fun j i => (∇ (f j) x) i) l (𝓝 (fun i => (∇ g x) i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have h := convex_fderiv_apply_limit hf hd hg hlim (EuclideanSpace.single i 1)
    simpa only [← inner_gradient_left, EuclideanSpace.inner_single_right, one_mul, conj_trivial] using h
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp hp

lemma normSmooth_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    Tendsto (fun j => normSmooth g (shrinkingBump n j) x) atTop (𝓝 (g x)) := by
  obtain ⟨C, hC⟩ := seminorm_lipschitz n g
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun j => normSmooth_dist_le g _ hC x)
    (by simpa only [mul_zero, shrinkingBump] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C : ℝ))

lemma normSmooth_gradient_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) {x : Space n}
    (hx : DifferentiableAt ℝ (g : Space n → ℝ) x) :
    Tendsto (fun j => ∇ (normSmooth g (shrinkingBump n j)) x) atTop (𝓝 (∇ (g : Space n → ℝ) x)) :=
  convex_gradient_limit (fun j => normSmooth_convex g _)
    (fun j => (normSmooth_contDiff g _).differentiable (by norm_num) x) hx (normSmooth_tendsto g)

end PettyProjection.Spherical
end

end OAI
