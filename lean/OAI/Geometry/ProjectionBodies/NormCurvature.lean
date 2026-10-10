import OAI.Geometry.ProjectionBodies.SphericalGap

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

/-- Intersection of the actual supporting constraints, with no evenness or
convexity condition on the constraint function. -/
def wulff {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  {x | ∀ u : Sphere n, ⟪(u : Space n),x⟫ ≤ s u}

lemma wulff_closed {n : ℕ} (s : Sphere n → ℝ) : IsClosed (wulff s) := by
  unfold wulff
  rw [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)

lemma wulff_convex {n : ℕ} (s : Sphere n → ℝ) : Convex ℝ (wulff s) := by
  intro x hx y hy a b ha hb hab u
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  calc
    _ ≤ a*s u+b*s u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
      (mul_le_mul_of_nonneg_left (hy u) hb)
    _ = s u := by rw [← add_mul,hab,one_mul]

lemma closedBall_subset_wulff {n : ℕ} {s : Sphere n → ℝ} {r : ℝ}
    (hr : ∀ u, r ≤ s u) : closedBall (0 : Space n) r ⊆ wulff s := by
  intro x hx u
  calc
    _ ≤ ‖(u : Space n)‖*‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_coe,one_mul]
    _ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    _ ≤ s u := hr u

lemma wulff_subset_closedBall {n : ℕ} {s : Sphere n → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ u, s u ≤ R) : wulff s ⊆ closedBall (0 : Space n) R := by
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_cases h : x = 0
  · simpa [h] using hR
  · let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩
    have hu : ⟪(u : Space n),x⟫ = ‖x‖ := by
      dsimp only [u]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    exact hu ▸ (hx u).trans (hs u)

lemma positive_constraint_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u, m ≤ s u ∧ s u ≤ M := by
  have hne : (univ : Set (Sphere n)).Nonempty := by
    obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
    exact ⟨⟨u,hu⟩,mem_univ _⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn hne s.continuous.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_univ.exists_isMaxOn hne s.continuous.continuousOn
  exact ⟨s u,s v,hs u,hs v,fun w => ⟨hu (mem_univ w),hv (mem_univ w)⟩⟩

lemma wulff_nhds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulff s ∈ 𝓝 (0 : Space n) := by
  obtain ⟨m,M,hm,_,hb⟩ := positive_constraint_bounds s hs
  exact Metric.mem_nhds_iff.mpr ⟨m,hm,ball_subset_closedBall.trans
    (closedBall_subset_wulff (fun u => (hb u).1))⟩

lemma wulff_compact {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulff s) := by
  obtain ⟨m,M,_,hM,hb⟩ := positive_constraint_bounds s hs
  exact (isCompact_closedBall (0 : Space n) M).of_isClosed_subset (wulff_closed _)
    (wulff_subset_closedBall hM.le (fun u => (hb u).2))

lemma wulff_body {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsConvexBody (wulff s) :=
  ⟨wulff_compact s hs,wulff_convex s,⟨0,mem_interior_iff_mem_nhds.mpr (wulff_nhds s hs)⟩⟩

lemma wulff_support {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) :
    wulff (fun u : Sphere n => support K u) = K := by
  ext x
  rw [mem_iff_inner_le_support hK hc hKn]
  constructor
  · intro h u
    by_cases hu : u = 0
    · subst u
      obtain ⟨y,hy,he⟩ := support_attained hK hKn 0
      simpa only [inner_zero_left] using he.ge
    · let v : Sphere n := ⟨‖u‖⁻¹ • u, by
        rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩
      have he : u = ‖u‖ • (v : Space n) := by dsimp [v]; rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hu)]
      rw [he,real_inner_smul_left,support_smul hK hKn (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
  · intro h u; exact h u

/-- Compact coefficient set of the maximum formula. -/
def wulffCoefficients {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  range (fun u : Sphere n => (s u)⁻¹ • (u : Space n))

def wulffMax {n : ℕ} (s : Sphere n → ℝ) (x : Space n) : ℝ :=
  support (wulffCoefficients s) x

lemma wulffCoefficients_compact {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulffCoefficients s) :=
  isCompact_range ((s.continuous.inv₀ (fun u => (hs u).ne')).smul continuous_subtype_val)

lemma wulffCoefficients_nonempty {n : ℕ} [NeZero n] (s : Sphere n → ℝ) :
    (wulffCoefficients s).Nonempty := by
  obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨_,⟨⟨u,hu⟩,rfl⟩⟩

lemma wulffMax_attained {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : ∃ u : Sphere n, wulffMax s x = ⟪x,(u : Space n)⟫ / s u := by
  obtain ⟨y,⟨u,rfl⟩,he⟩ := support_attained (wulffCoefficients_compact s hs)
    (wulffCoefficients_nonempty s) x
  exact ⟨u,by simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using he⟩

lemma le_wulffMax {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) (u : Sphere n) : ⟪x,(u : Space n)⟫ / s u ≤ wulffMax s x := by
  simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using
    inner_le_support (wulffCoefficients_compact s hs) (mem_range_self u) x

lemma wulffMax_pos {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    {x : Space n} (hx : x ≠ 0) : 0 < wulffMax s x := by
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he : ⟪x,(u : Space n)⟫ = ‖x‖ := by
    dsimp only [u]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  apply lt_of_lt_of_le _ (le_wulffMax s hs x u)
  rw [he]
  exact div_pos (norm_pos_iff.mpr hx) (hs u)

lemma wulffMax_zero {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulffMax s (0 : Space n) = 0 := by
  obtain ⟨u,he⟩ := wulffMax_attained s hs 0
  simpa only [inner_zero_left,zero_div] using he

lemma mem_smul_wulff {n : ℕ} {s : Sphere n → ℝ} {a : ℝ} (ha : 0 < a) {x : Space n} :
    x ∈ a • wulff s ↔ ∀ u : Sphere n, ⟪x,(u : Space n)⟫ ≤ a*s u := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  change (∀ u : Sphere n, ⟪(u : Space n),a⁻¹ • x⟫ ≤ s u) ↔ _
  simp_rw [real_inner_smul_right,real_inner_comm (y := x),← div_eq_inv_mul,div_le_iff₀ ha]
  simp only [mul_comm]

lemma gauge_wulff_eq_max {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : gauge (wulff s) x = wulffMax s x := by
  by_cases hx : x = 0
  · subst x; rw [gauge_zero,wulffMax_zero s hs]
  have hp := wulffMax_pos s hs hx
  have hmem : x ∈ wulffMax s x • wulff s := by
    apply (mem_smul_wulff hp).mpr
    intro u
    have h := (div_le_iff₀ (hs u)).mp (le_wulffMax s hs x u)
    simpa only [mul_comm] using h
  apply le_antisymm (gauge_le_of_mem hp.le hmem)
  rw [gauge_def]
  refine le_csInf (s := {r : ℝ | r ∈ Ioi 0 ∧ x ∈ r • wulff s})
    ⟨wulffMax s x,hp,hmem⟩ ?_
  rintro a ⟨ha,hax⟩
  obtain ⟨u,he⟩ := wulffMax_attained s hs x
  rw [he]
  exact (div_le_iff₀ (hs u)).mpr ((mem_smul_wulff ha).mp hax u)

lemma gauge_ae_differentiable_sphere {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∀ᵐ (u : Sphere n) ∂Spherical.sigma n, DifferentiableAt ℝ (gauge K) (u : Space n) := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  apply Spherical.sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hh : DifferentiableAt ℝ (fun x : Space n => r⁻¹ * gauge K (r • x)) (u : Space n) :=
    (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_mul r⁻¹
  have he : (fun x : Space n => r⁻¹ * gauge K (r • x)) = gauge K := by
    funext x
    rw [gauge_smul_of_nonneg (α := ℝ) hr.le,smul_eq_mul,← mul_assoc,
      inv_mul_cancel₀ hr.ne',one_mul]
  rwa [he] at hh

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma rotDeriv_comp_scalar {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} {G : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hG : Differentiable ℝ G) (x : Space n) :
    rotDeriv T (G ∘ f) x = deriv G (f x) * rotDeriv T f x := by
  have h := (hG (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt
  simp only [rotDeriv, h.fderiv, smul_apply, smul_eq_mul]

lemma energy_comp_relation {n : ℕ} (f : Space n → ℝ) (G I : ℝ → ℝ) (b : ℝ)
    (hf : Differentiable ℝ f) (hG : Differentiable ℝ G) (hI : Differentiable ℝ I)
    (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    energy (G ∘ f) (G ∘ f) = b ^ 2 * energy (I ∘ f) f := by
  unfold energy
  simp_rw [rotDeriv_comp_scalar _ hf hG, rotDeriv_comp_scalar _ hf hI]
  have he (i j : Fin n) :
      (fun u : Sphere n => deriv G (f u) * rotDeriv (generator n i j) f u *
        (deriv G (f u) * rotDeriv (generator n i j) f u)) =
      (fun u : Sphere n => b ^ 2 *
        (deriv I (f u) * rotDeriv (generator n i j) f u * rotDeriv (generator n i j) f u)) := by
    funext u
    calc
      _ = deriv G (f u) ^ 2 * (rotDeriv (generator n i j) f u) ^ 2 := by ring
      _ = _ := by rw [hrel]; ring
  simp_rw [he, mean, integral_const_mul]
  simp only [← Finset.mul_sum]
  ring

lemma smooth_convex_energy_bound {n : ℕ} [NeZero n]
    {f : Space n → ℝ} {G I : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f)
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    energy (G ∘ f) (G ∘ f) ≤ ((n : ℝ) - 1) * b ^ 2 *
      mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) := by
  have hfc : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hr := energy_comp_relation f G I b (hf.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hI.differentiable (by norm_num)) hrel
  rw [hr]
  have hibp := mean_casimir (hI.comp hfc) hf
  have hcont : Continuous (fun u : Sphere n => I (f u) * casimir f u) := by
    apply (hI.continuous.comp (hf.continuous.comp continuous_subtype_val)).mul
    unfold casimir
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ =>
        (continuous_rotDeriv _ (contDiff_rotDeriv _ hf)).comp continuous_subtype_val)
  have hcont' : Continuous (fun u : Sphere n =>
      -((n : ℝ) - 1) * (I (f u) * fderiv ℝ f u u)) :=
    continuous_const.mul ((hI.continuous.comp (hf.continuous.comp continuous_subtype_val)).mul
      ((hf.continuous_fderiv (by norm_num)).comp continuous_subtype_val |>.clm_apply continuous_subtype_val))
  have hle : mean (fun u : Sphere n => -((n : ℝ) - 1) * (I (f u) * fderiv ℝ f u u)) ≤
      mean (fun u : Sphere n => I (f u) * casimir f u) := by
    apply integral_mono (continuous_integrable hcont') (continuous_integrable hcont)
    intro u
    have h := mul_le_mul_of_nonneg_left (convex_casimir_lower hf hc u) (hpos (f u))
    nlinarith
  rw [mean, integral_const_mul] at hle
  change -((n : ℝ) - 1) * mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) ≤ _ at hle
  simp only [Function.comp_apply] at hibp
  rw [hibp] at hle
  have h := mul_le_mul_of_nonneg_left hle (sq_nonneg b)
  nlinarith

lemma smooth_convex_curvature {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} {G I : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (heven : Function.Even f)
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    (2 * n : ℝ) * variance (fun u : Sphere n => G (f u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (G ∘ f) (hG.continuous.comp hf.continuous)))‖ ^ 2 ≤
      ((n : ℝ) - 1) * b ^ 2 * mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) := by
  have he : Function.Even (G ∘ f) := fun x => by simp only [Function.comp_apply]; rw [heven x]
  exact (even_spectral_gap hn (hG.comp (hf.of_le (by norm_num))) he).trans
    (smooth_convex_energy_bound hf hc hG hI hpos hrel)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma continuous_mean {n : ℕ} [NeZero n] :
    Continuous (fun f : C(Sphere n, ℝ) => mean f) := by
  have he : (fun f : C(Sphere n, ℝ) => mean f) =
      (fun f => ⟪toH n f, toH n (ContinuousMap.const (Sphere n) 1)⟫) := by
    funext f
    rw [inner_toH]
    simp only [ContinuousMap.const_apply, mul_one]
  rw [he]
  exact (toH n).continuous.inner continuous_const

lemma continuous_variance {n : ℕ} [NeZero n] :
    Continuous (fun f : C(Sphere n, ℝ) => variance f) := by
  have he : (fun f : C(Sphere n, ℝ) => variance f) =
      (fun f => ‖toH n f‖ ^ 2 - (mean f) ^ 2) := by
    funext f
    rw [norm_toH_sq]
    rfl
  rw [he]
  exact ((toH n).continuous.norm.pow 2).sub (continuous_mean.pow 2)

def shrinkingBump (n j : ℕ) : ContDiffBump (0 : Space n) where
  rIn := (1 / ((j : ℝ) + 1)) / 2
  rOut := 1 / ((j : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith

lemma seminorm_approximation {n : ℕ} (g : Seminorm ℝ (Space n)) :
    ∃ F R : ℕ → C(Sphere n, ℝ),
      (∀ j, F j = restrictContinuous (normSmooth g (shrinkingBump n j))
        (normSmooth_contDiff g _).continuous) ∧
      (∀ j u, R j u = fderiv ℝ (normSmooth g (shrinkingBump n j)) u u) ∧
      Tendsto F atTop (𝓝 (restrictContinuous g (seminorm_continuous n g))) ∧
      Tendsto R atTop (𝓝 (restrictContinuous g (seminorm_continuous n g))) := by
  let F : ℕ → C(Sphere n, ℝ) := fun j => restrictContinuous
    (normSmooth g (shrinkingBump n j)) (normSmooth_contDiff g _).continuous
  let R : ℕ → C(Sphere n, ℝ) := fun j => ⟨fun u =>
    fderiv ℝ (normSmooth g (shrinkingBump n j)) u u,
    ((normSmooth_contDiff g _).continuous_fderiv (by norm_num)).comp continuous_subtype_val
      |>.clm_apply continuous_subtype_val⟩
  refine ⟨F, R, fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := seminorm_lipschitz n g
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j =>
      (ContinuousMap.dist_le (mul_nonneg C.coe_nonneg (shrinkingBump n j).rOut_pos.le)).mpr
        (fun u => normSmooth_dist_le g _ hC u))
      (by simpa only [mul_zero, shrinkingBump] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C : ℝ))
  · obtain ⟨C, hC⟩ := seminorm_lipschitz n g
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j =>
      (ContinuousMap.dist_le (mul_nonneg (mul_nonneg (by norm_num) C.coe_nonneg)
        (shrinkingBump n j).rOut_pos.le)).mpr
        (fun u => normSmooth_radial_dist_le g _ hC u))
      (by simpa only [mul_zero, shrinkingBump] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C : ℝ))

/-- The nonsmooth curvature inequality, proved by actual even convolution of
an arbitrary seminorm. No smoothness, homogeneity of approximants, or assumed
spectral interface is required. -/
theorem seminorm_curvature {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) {G I : ℝ → ℝ} {b : ℝ}
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    (2 * n : ℝ) * variance (fun u : Sphere n => G (g u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (G ∘ g) (hG.continuous.comp (seminorm_continuous n g))))‖ ^ 2 ≤
      ((n : ℝ) - 1) * b ^ 2 * mean (fun u : Sphere n => I (g u) * g u) := by
  obtain ⟨F, R, hF, hR, hFt, hRt⟩ := seminorm_approximation g
  let Gc : C(ℝ, ℝ) := ⟨G, hG.continuous⟩
  let Ic : C(ℝ, ℝ) := ⟨I, hI.continuous⟩
  have hGt := Gc.continuous_postcomp.tendsto _ |>.comp hFt
  have hIt := Ic.continuous_postcomp.tendsto _ |>.comp hFt
  have hl := (continuous_variance.tendsto _ |>.comp hGt).const_mul (2 * n : ℝ)
  have hq := (((Q n).continuous.comp (toH n).continuous).tendsto _ |>.comp hGt).norm.pow 2
  have hr := (continuous_mean.tendsto _ |>.comp (hIt.mul hRt)).const_mul
    (((n : ℝ) - 1) * b ^ 2)
  apply le_of_tendsto_of_tendsto' (hl.add (hq.const_mul (2 * n + 8 : ℝ))) hr
  intro j
  have h := smooth_convex_curvature hn (normSmooth_contDiff g (shrinkingBump n j))
    (normSmooth_convex g _) (normSmooth_even g _) hG hI hpos hrel
  simp only [Function.comp_apply, hF, hR, Gc, Ic, ContinuousMap.coe_mk,
    ContinuousMap.coe_mul, Pi.mul_def,
    ContinuousMap.comp, restrictContinuous]
  convert h using 1
  rfl

end PettyProjection.Spherical
end

end OAI
