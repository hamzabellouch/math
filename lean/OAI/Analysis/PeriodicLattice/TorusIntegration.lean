import OAI.Analysis.PeriodicLattice.TorusDerivatives

namespace OAI

/-! Periodic integration and differentiation identities. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingTorusIntegration {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace TorusCalculus

open scoped ContDiff Topology
open Filter Set MeasureTheory

instance volume_haar : torusVolume.IsAddHaarMeasure := by
  dsimp [torusVolume]
  infer_instance

section SpatialSlices
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

omit [NormedSpace ℝ A] in
theorem slice_continuous_iff (F : Field A) (t : ℝ) :
    Continuous (F t) ↔ Continuous (spaceLift F t) :=
  mk_isOpenQuotientMap.isQuotientMap.continuous_iff

theorem slice_contDiff_spaceD {F : Field A} {t : ℝ} {n : WithTop ℕ∞}
    (hF : ContDiff ℝ (n + 1) (spaceLift F t)) (i : Fin 3) :
    ContDiff ℝ n (spaceLift (spaceD i F) t) := by
  have hd : Differentiable ℝ (spaceLift F t) := hF.differentiable (by simp)
  have heq : spaceLift (spaceD i F) t = fun x =>
      (fderiv ℝ (spaceLift F t) x) (EuclideanSpace.single i 1) := by
    funext x
    exact spaceD_eq_fderiv i x hd
  rw [heq]
  exact (hF.fderiv_right le_rfl).clm_apply contDiff_const

theorem translation_hasDerivAt {F : Field A} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (q : Torus) (i : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => F t (q + torusMk (EuclideanSpace.single i s)))
      (spaceD i F t (q + torusMk (EuclideanSpace.single i s))) s := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp only [← mk_add, spaceD_eq_fderiv i _ hF]
  have hcv : HasDerivAt (fun r : ℝ => x + EuclideanSpace.single i r)
      (EuclideanSpace.single i 1) s := by
    have heq : (fun r : ℝ => x + EuclideanSpace.single i r) =
        (fun r : ℝ => x + r • EuclideanSpace.single i 1) := by
      funext r
      rw [single_eq_smul i r]
    rw [heq]
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id s).smul_const (EuclideanSpace.single i 1)).const_add x)
  exact (hF _).hasFDerivAt.comp_hasDerivAt s hcv

theorem integral_spaceD_of_continuous {F : Field A} {t : ℝ} (i : Fin 3)
    (hF : Differentiable ℝ (spaceLift F t))
    (hFc : Continuous (F t)) (hDc : Continuous (spaceD i F t)) :
    (∫ q, spaceD i F t q ∂torusVolume) = 0 := by
  have hFi : Integrable (F t) torusVolume := hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hDc.continuousOn
  let G : ℝ → Torus → A := fun s q => F t (q + torusMk (EuclideanSpace.single i s))
  let G' : ℝ → Torus → A := fun s q => spaceD i F t (q + torusMk (EuclideanSpace.single i s))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := torusVolume)
    (F := G) (F' := G') (s := univ) (x₀ := 0) (bound := fun _ => C)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun s =>
      (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable))
    (by simpa [G] using hFi)
    ((hDc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun q s _ => hC _ (mem_univ _)))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun q s _ =>
      translation_hasDerivAt hF q i s))
  have heq : (fun s => ∫ q, G s q ∂torusVolume) =
      fun _ : ℝ => ∫ q, F t q ∂torusVolume := by
    funext s
    exact integral_add_right_eq_self _ _
  rw [heq] at h
  have hz := h.2.unique (hasDerivAt_const (0 : ℝ) (∫ q, F t q ∂torusVolume))
  simpa [G'] using hz

theorem integral_spaceD_C1 {F : Field A} {t : ℝ}
    (hF : ContDiff ℝ 1 (spaceLift F t)) (i : Fin 3) :
    (∫ q, spaceD i F t q ∂torusVolume) = 0 :=
  integral_spaceD_of_continuous i (hF.differentiable one_ne_zero)
    ((slice_continuous_iff F t).mpr hF.continuous)
    ((slice_continuous_iff (spaceD i F) t).mpr
      (slice_contDiff_spaceD (n := 0) (by simpa using hF) i).continuous)

theorem spaceD_add {F G : Field A} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (hG : Differentiable ℝ (spaceLift G t))
    (i : Fin 3) (q : Torus) :
    spaceD i (F + G) t q = spaceD i F t q + spaceD i G t q := by
  have h := ((translation_hasDerivAt hF q i 0).fun_add
    (translation_hasDerivAt hG q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD, Pi.add_apply] using h

theorem spaceD_sub {F G : Field A} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (hG : Differentiable ℝ (spaceLift G t))
    (i : Fin 3) (q : Torus) :
    spaceD i (F - G) t q = spaceD i F t q - spaceD i G t q := by
  have h := ((translation_hasDerivAt hF q i 0).fun_sub
    (translation_hasDerivAt hG q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD, Pi.sub_apply] using h

end SpatialSlices

section InnerProducts
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

theorem spaceD_inner {F G : Field A} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (hG : Differentiable ℝ (spaceLift G t))
    (i : Fin 3) (q : Torus) :
    spaceD i (fun t q => inner ℝ (F t q) (G t q)) t q =
      inner ℝ (F t q) (spaceD i G t q) + inner ℝ (spaceD i F t q) (G t q) := by
  have h := (HasDerivAt.inner ℝ (translation_hasDerivAt hF q i 0)
    (translation_hasDerivAt hG q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD] using h

theorem integration_by_parts {F G : Field A} {t : ℝ}
    (hF : ContDiff ℝ 1 (spaceLift F t)) (hG : ContDiff ℝ 1 (spaceLift G t))
    (i : Fin 3) :
    (∫ q, inner ℝ (F t q) (spaceD i G t q) ∂torusVolume) =
      -(∫ q, inner ℝ (spaceD i F t q) (G t q) ∂torusVolume) := by
  have hP : ContDiff ℝ 1 (spaceLift (fun t q => inner ℝ (F t q) (G t q)) t) := hF.inner ℝ hG
  have hFc := (slice_continuous_iff F t).mpr hF.continuous
  have hGc := (slice_continuous_iff G t).mpr hG.continuous
  have hDF := (slice_continuous_iff (spaceD i F) t).mpr
    (slice_contDiff_spaceD (n := 0) (by simpa using hF) i).continuous
  have hDG := (slice_continuous_iff (spaceD i G) t).mpr
    (slice_contDiff_spaceD (n := 0) (by simpa using hG) i).continuous
  have h := integral_spaceD_C1 hP i
  simp_rw [spaceD_inner (hF.differentiable one_ne_zero) (hG.differentiable one_ne_zero)] at h
  rw [integral_add
    ((hFc.inner hDG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hDF.inner hGc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at h
  linarith

theorem integral_inner_laplacian {F : Field A} {t : ℝ}
    (hF : ContDiff ℝ 2 (spaceLift F t)) :
    (∫ q, inner ℝ (F t q) (laplacian F t q) ∂torusVolume) =
      -∑ i : Fin 3, ∫ q, ‖spaceD i F t q‖ ^ 2 ∂torusVolume := by
  have hF₁ : ContDiff ℝ 1 (spaceLift F t) := hF.of_le (by norm_num)
  have hD₁ (i : Fin 3) : ContDiff ℝ 1 (spaceLift (spaceD i F) t) :=
    slice_contDiff_spaceD (n := 1) (by convert hF using 1; norm_num) i
  have hFi := (slice_continuous_iff F t).mpr hF.continuous
  have hDDi (i : Fin 3) := (slice_continuous_iff (spaceD i (spaceD i F)) t).mpr
    (slice_contDiff_spaceD (n := 0) (by simpa using hD₁ i) i).continuous
  simp_rw [laplacian, inner_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (hFi.inner (hDDi i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp_rw [integration_by_parts hF₁ (hD₁ _), real_inner_self_eq_norm_sq]
  exact Finset.sum_neg_distrib _

end InnerProducts

end TorusCalculus

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

theorem spaceD_congr_slice {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F G : Field A} {t : ℝ} (h : ∀ q, F t q = G t q) (i : Fin 3) (q : Torus) :
    spaceD i F t q = spaceD i G t q := by
  unfold spaceD
  simp_rw [h]

theorem laplacian_sub {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F G : Field A} {t : ℝ}
    (hF : ContDiff ℝ 2 (spaceLift F t)) (hG : ContDiff ℝ 2 (spaceLift G t)) (q : Torus) :
    laplacian (F - G) t q = laplacian F t q - laplacian G t q := by
  unfold laplacian
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [spaceD_congr_slice (G := spaceD i F - spaceD i G)
    (fun x => spaceD_sub (hF.differentiable (by norm_num)) (hG.differentiable (by norm_num)) i x)]
  exact spaceD_sub
    ((slice_contDiff_spaceD (n := 1) (by convert hF using 1; norm_num) i).differentiable one_ne_zero)
    ((slice_contDiff_spaceD (n := 1) (by convert hG using 1; norm_num) i).differentiable one_ne_zero) i q

theorem eq_zero_of_integral_norm_sq_eq_zero {A : Type*} [NormedAddCommGroup A]
    {F : Torus → A} (hF : Continuous F)
    (hzero : (∫ q, ‖F q‖ ^ 2 ∂torusVolume) = 0) : ∀ q, F q = 0 := by
  have hc : Continuous (fun q => ‖F q‖ ^ 2) := hF.norm.pow 2
  have ha := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg ‖F q‖)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hzero
  have heq := (hc.ae_eq_iff_eq torusVolume continuous_const).mp ha
  intro q
  have hq : ‖F q‖ ^ 2 = 0 := congrFun heq q
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hq)

theorem spatially_constant_of_partials_zero {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] {F : Field A} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (hzero : ∀ i q, spaceD i F t q = 0)
    (q r : Torus) : F t q = F t r := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  obtain ⟨y, rfl⟩ := mk_surjective r
  apply is_const_of_fderiv_eq_zero hF _ x y
  intro z
  have hz : (fderiv ℝ (spaceLift F t) z).toLinearMap = 0 := by
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    change (fderiv ℝ (spaceLift F t) z) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = 0
    rw [EuclideanSpace.basisFun_apply, ← spaceD_eq_fderiv i z hF, hzero]
  ext w
  exact DFunLike.congr_fun hz w

theorem harmonic_constant {F : ScalarField} {t : ℝ}
    (hF : ContDiff ℝ 2 (spaceLift F t)) (hΔ : ∀ q, laplacian F t q = 0)
    (q r : Torus) : F t q = F t r := by
  have hE := integral_inner_laplacian hF
  simp only [hΔ, inner_zero_right, integral_zero] at hE
  have hI : ∀ i : Fin 3, (∫ q, ‖spaceD i F t q‖ ^ 2 ∂torusVolume) = 0 := by
    have hsum : (∑ i : Fin 3, ∫ q, ‖spaceD i F t q‖ ^ 2 ∂torusVolume) = 0 := by
      linarith
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      integral_nonneg (fun q => sq_nonneg ‖spaceD i F t q‖))).mp hsum i (Finset.mem_univ i)
  apply spatially_constant_of_partials_zero (hF.differentiable (by norm_num)) _ q r
  intro i
  exact eq_zero_of_integral_norm_sq_eq_zero
    ((slice_continuous_iff (spaceD i F) t).mpr
      (slice_contDiff_spaceD (n := 1) (by convert hF using 1; norm_num) i).continuous) (hI i)

theorem harmonic_meanZero_eq_zero {F : ScalarField} {t : ℝ}
    (hF : ContDiff ℝ 2 (spaceLift F t)) (hΔ : ∀ q, laplacian F t q = 0)
    (hmean : (∫ q, F t q ∂torusVolume) = 0) (q : Torus) : F t q = 0 := by
  have heq : F t = fun _ => F t q := funext (fun r => harmonic_constant hF hΔ r q)
  rw [heq, integral_const] at hmean
  simpa using hmean

theorem poisson_unique {g : VectorField} {φ : ScalarField}
    (hφ : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ 2 (spaceLift φ t)) (hmean : MeanZero φ)
    (hΔ : ∀ t : ℝ, 0 ≤ t → ∀ q, laplacian φ t q = divergence g t q) :
    UniqueMeanZeroPoisson g φ := by
  intro ψ hψ hψmean hψΔ t ht q
  have hF : ContDiff ℝ 2 (spaceLift (ψ - φ) t) := (hψ t ht).sub (hφ t ht)
  have hzero : (ψ - φ) t q = 0 := harmonic_meanZero_eq_zero hF
    (fun r => by rw [laplacian_sub (hψ t ht) (hφ t ht), hψΔ t ht, hΔ t ht, sub_self])
    (by
      change (∫ r, ψ t r - φ t r ∂torusVolume) = 0
      rw [integral_sub
        (((slice_continuous_iff ψ t).mpr (hψ t ht).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (((slice_continuous_iff φ t).mpr (hφ t ht).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)), hψmean t ht, hmean t ht, sub_self]) q
  exact sub_eq_zero.mp hzero

end TorusCalculus

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

section ClassicalOperations

theorem cylinder_slice_continuous {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Field A} (hF : CylinderContinuous F) {t : ℝ} (ht : 0 ≤ t) : Continuous (F t) := by
  apply continuousOn_univ.mp
  exact (hF t ht).comp (continuous_const.prodMk continuous_id).continuousOn
    (fun q _ => ⟨⟨ht, le_rfl⟩, Set.mem_univ q⟩)

theorem spaceD_component {U : VectorField} {t : ℝ}
    (hU : Differentiable ℝ (spaceLift U t)) (i j : Fin 3) (q : Torus) :
    spaceD i (fun t q => U t q j) t q = spaceD i U t q j := by
  have h := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt 0
    (translation_hasDerivAt hU q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD, Function.comp_def, PiLp.proj_apply] using h

theorem contDiff_component_slice {U : VectorField} {t : ℝ} {n : WithTop ℕ∞}
    (hU : ContDiff ℝ n (spaceLift U t)) (i : Fin 3) :
    ContDiff ℝ n (spaceLift (fun t q => U t q i) t) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp hU

theorem spaceD_smul_slice {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {c : ScalarField} {F : Field A} {t : ℝ}
    (hc : Differentiable ℝ (spaceLift c t)) (hF : Differentiable ℝ (spaceLift F t))
    (i : Fin 3) (q : Torus) :
    spaceD i (fun t q => c t q • F t q) t q =
      spaceD i c t q • F t q + c t q • spaceD i F t q := by
  have h := ((translation_hasDerivAt hc q i 0).fun_smul
    (translation_hasDerivAt hF q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD, add_comm] using h

def transport (V W : VectorField) : VectorField := fun t q =>
  ∑ i : Fin 3, V t q i • spaceD i W t q

theorem transport_continuous {V W : VectorField} {t : ℝ}
    (hV : ContDiff ℝ 1 (spaceLift V t)) (hW : ContDiff ℝ 1 (spaceLift W t)) :
    Continuous (transport V W t) := by
  apply continuous_finsetSum _ (fun i _ => ?_)
  exact
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp ((slice_continuous_iff V t).mpr hV.continuous)).smul
    ((slice_continuous_iff (spaceD i W) t).mpr
      (slice_contDiff_spaceD (n := 0) (by simpa using hW) i).continuous)

theorem transport_eq_divergence_tensor {V W : VectorField} {t : ℝ}
    (hV : Differentiable ℝ (spaceLift V t)) (hW : Differentiable ℝ (spaceLift W t))
    (hdiv : ∀ q, divergence V t q = 0) (q : Torus) :
    (∑ i : Fin 3, spaceD i (fun t q => V t q i • W t q) t q) = transport V W t q := by
  have hc (i : Fin 3) : Differentiable ℝ (spaceLift (fun t q => V t q i) t) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).differentiable.comp hV
  simp_rw [spaceD_smul_slice (hc _) hW]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]
  change divergence V t q • W t q + transport V W t q = _
  rw [hdiv q, zero_smul, zero_add]

theorem integral_inner_transport {V W Z : VectorField} {t : ℝ}
    (hV : ContDiff ℝ 1 (spaceLift V t)) (hW : ContDiff ℝ 1 (spaceLift W t))
    (hZ : ContDiff ℝ 1 (spaceLift Z t)) (hdiv : ∀ q, divergence V t q = 0) :
    (∫ q, inner ℝ (W t q) (transport V Z t q) ∂torusVolume) =
      -(∫ q, inner ℝ (transport V W t q) (Z t q) ∂torusVolume) := by
  have hP (i : Fin 3) : ContDiff ℝ 1 (spaceLift (fun t q => V t q i • W t q) t) :=
    (contDiff_component_slice hV i).smul hW
  have hWc := (slice_continuous_iff W t).mpr hW.continuous
  have hZc := (slice_continuous_iff Z t).mpr hZ.continuous
  have hDc (i : Fin 3) := (slice_continuous_iff (spaceD i Z) t).mpr
    (slice_contDiff_spaceD (n := 0) (by simpa using hZ) i).continuous
  have hPc (i : Fin 3) := (slice_continuous_iff (fun t q => V t q i • W t q) t).mpr
    (hP i).continuous
  have hDPc (i : Fin 3) := (slice_continuous_iff (spaceD i (fun t q => V t q i • W t q)) t).mpr
    (slice_contDiff_spaceD (n := 0) (by simpa using hP i) i).continuous
  calc
    _ = ∑ i : Fin 3, ∫ q, inner ℝ (V t q i • W t q) (spaceD i Z t q) ∂torusVolume := by
      simp_rw [transport, inner_sum, inner_smul_right, real_inner_smul_left]
      rw [integral_finsetSum Finset.univ (fun i _ => by
        simpa only [real_inner_smul_left] using
          ((((hPc i).inner (hDc i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) : Integrable (fun q => inner ℝ (V t q i • W t q) (spaceD i Z t q)) torusVolume))]
    _ = ∑ i : Fin 3, -(∫ q, inner ℝ (spaceD i (fun t q => V t q i • W t q) t q) (Z t q)
          ∂torusVolume) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integration_by_parts (hP i) hZ i
    _ = -(∫ q, inner ℝ (∑ i : Fin 3, spaceD i (fun t q => V t q i • W t q) t q) (Z t q)
          ∂torusVolume) := by
      simp_rw [sum_inner]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        ((hDPc i).inner hZc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
      exact Finset.sum_neg_distrib _
    _ = _ := by
      simp_rw [transport_eq_divergence_tensor (hV.differentiable one_ne_zero)
        (hW.differentiable one_ne_zero) hdiv]

theorem integral_inner_transport_self {V W : VectorField} {t : ℝ}
    (hV : ContDiff ℝ 1 (spaceLift V t)) (hW : ContDiff ℝ 1 (spaceLift W t))
    (hdiv : ∀ q, divergence V t q = 0) :
    (∫ q, inner ℝ (W t q) (transport V W t q) ∂torusVolume) = 0 := by
  have h := integral_inner_transport hV hW hW hdiv
  have he : (∫ q, inner ℝ (transport V W t q) (W t q) ∂torusVolume) =
      (∫ q, inner ℝ (W t q) (transport V W t q) ∂torusVolume) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => real_inner_comm _ _)
  rw [he] at h
  linarith

theorem integral_inner_gradient {W : VectorField} {p : ScalarField} {t : ℝ}
    (hW : ContDiff ℝ 1 (spaceLift W t)) (hdiv : ∀ q, divergence W t q = 0)
    (hpc : Continuous (p t)) (hp : Differentiable ℝ (spaceLift p t))
    (hdp : Continuous (gradient p t)) :
    (∫ q, inner ℝ (W t q) (gradient p t q) ∂torusVolume) = 0 := by
  have hWc := (slice_continuous_iff W t).mpr hW.continuous
  have hD (i : Fin 3) : Continuous (spaceD i (fun t q => W t q i) t) :=
    (slice_continuous_iff _ t).mpr
      (slice_contDiff_spaceD (n := 0) (by simpa using contDiff_component_slice hW i) i).continuous
  have hDP (i : Fin 3) : Continuous (spaceD i p t) := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hdp
  have hrule (i : Fin 3) (q : Torus) :
      spaceD i (fun t q => W t q i * p t q) t q =
        spaceD i (fun t q => W t q i) t q * p t q + W t q i * spaceD i p t q :=
    spaceD_smul_slice ((contDiff_component_slice hW i).differentiable one_ne_zero) hp i q
  have hI (i : Fin 3) : (∫ q, W t q i * spaceD i p t q ∂torusVolume) =
      -(∫ q, spaceD i (fun t q => W t q i) t q * p t q ∂torusVolume) := by
    have hPdiff : Differentiable ℝ (spaceLift (fun t q => W t q i * p t q) t) :=
      ((contDiff_component_slice hW i).differentiable one_ne_zero).mul hp
    have hPcont : Continuous (fun q => W t q i * p t q) := ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hWc).mul hpc
    have hPderiv : Continuous (spaceD i (fun t q => W t q i * p t q) t) := by
      change Continuous (fun q => spaceD i (fun t q => W t q i * p t q) t q)
      simp_rw [hrule]
      exact ((hD i).mul hpc).add (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hWc).mul (hDP i))
    have h := integral_spaceD_of_continuous i hPdiff hPcont hPderiv
    simp_rw [hrule] at h
    rw [integral_add (f := fun q => spaceD i (fun t q => W t q i) t q * p t q)
      (g := fun q => W t q i * spaceD i p t q)
      ((((hD i).mul hpc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) : Integrable (fun q => spaceD i (fun t q => W t q i) t q * p t q) torusVolume)
      (((((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hWc).mul (hDP i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) : Integrable (fun q => W t q i * spaceD i p t q) torusVolume)] at h
    linarith
  have hinner (q : Torus) : inner ℝ (W t q) (gradient p t q) =
      ∑ i : Fin 3, W t q i * spaceD i p t q := by
    simp [PiLp.inner_apply, gradient, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum (f := fun i q => W t q i * spaceD i p t q) Finset.univ (fun i _ =>
    (((((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hWc).mul (hDP i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) : Integrable (fun q => W t q i * spaceD i p t q) torusVolume))]
  simp_rw [hI]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum
    (f := fun i q => spaceD i (fun t q => W t q i) t q * p t q) Finset.univ (fun i _ =>
    ((((hD i).mul hpc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) : Integrable (fun q => spaceD i (fun t q => W t q i) t q * p t q) torusVolume))]
  simp_rw [← Finset.sum_mul]
  change -(∫ q, divergence W t q * p t q ∂torusVolume) = 0
  simp only [hdiv, zero_mul, integral_zero, neg_zero]

end ClassicalOperations
end TorusCalculus

end
end PeriodicLattice

end OAI
