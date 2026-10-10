import Mathlib
import OAI.Geometry.BallPacking.Necessity.CauchyDuality

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open Function MeasureTheory
open scoped BoundedContinuousFunction
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cauchyTransform_holder_complexCurl {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    complexCauchyCurl (cauchyTransform g) x = (2*Complex.I) • g x := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  rw [complexCauchyCurl_dual
    ((cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg).differentiable (by simp))]
  have he : (fun w => l (cauchyTransform g w)) = cauchyTransform (fun w => l (g w)) :=
    funext (cauchyTransform_dual hg hc l)
  rw [he]
  have hMl (w : ℂ) : ‖l (g w)‖ ≤ ‖l‖*M :=
    (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _))
  have hHl (w z : ℂ) : ‖l (g w)-l (g z)‖ ≤ (‖l‖*H)*‖w-z‖^((1:ℝ)/3) := by
    rw [←map_sub]
    exact (l.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hHg w z) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm)
  have hh := cauchyTransform_holder_curlNecessity (g := fun w => l (g w))
    (l.continuous.comp hg) (hc.comp_left l.map_zero)
    hMl (mul_nonneg (norm_nonneg _) hH) hHl x
  simpa only [map_smul,smul_eq_mul] using hh

lemma closedBall_subset_exterior {R r : ℝ} {x : ℂ} (hx : R+r < ‖x‖) :
    Metric.closedBall x r ⊆ {z : ℂ | R < ‖z‖} := by
  intro z hz
  have hh : ‖x‖ ≤ ‖z‖ + r := by
    have ht := norm_sub_le x z
    have hz' : ‖x-z‖ ≤ r := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    linarith [norm_le_insert' x z]
  change R < ‖z‖
  linarith

omit [CompleteSpace E] in
lemma holomorphic_exterior_deriv_bound {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x : ℂ} (hx : R+1 < ‖x‖) :
    ‖deriv f x‖ ≤ M := by
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ)<1) (hd.diffContOnCl_ball (closedBall_subset_exterior hx))
    (fun z _ => hM z)

lemma holomorphic_exterior_secondDeriv_bound {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x : ℂ} (hx : R+1 < ‖x‖) :
    ‖deriv (deriv f) x‖ ≤ 2*M := by
  simpa [iteratedDeriv_succ] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 (by norm_num : (0:ℝ)<1)
    (hd.diffContOnCl_ball (closedBall_subset_exterior hx)) (fun z _ => hM z)

omit [CompleteSpace E] in
lemma real_fderiv_eq_complex_deriv {f : ℂ → E} {x : ℂ}
    (hx : DifferentiableAt ℂ f x) :
    fderiv ℝ f x = ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ) :=
  (hx.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv

omit [CompleteSpace E] in
lemma real_fderiv_norm_eq_deriv {f : ℂ → E} {x : ℂ} (hx : DifferentiableAt ℂ f x) :
    ‖fderiv ℝ f x‖ = ‖deriv f x‖ := by
  rw [hx.fderiv_restrictScalars ℝ,ContinuousLinearMap.norm_restrictScalars,
    ←norm_deriv_eq_norm_fderiv]

omit [CompleteSpace E] in
lemma real_fderiv_sub_norm_eq_deriv {f : ℂ → E} {x y : ℂ}
    (hx : DifferentiableAt ℂ f x) (hy : DifferentiableAt ℂ f y) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ = ‖deriv f x-deriv f y‖ := by
  rw [real_fderiv_eq_complex_deriv hx,real_fderiv_eq_complex_deriv hy,
    ←ContinuousLinearMap.restrictScalars_sub,ContinuousLinearMap.norm_restrictScalars]
  have he : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x) -
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f y) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x-deriv f y) := by
    ext
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_sub]
  rw [he]
  simp

lemma holomorphic_exterior_fderiv_lipschitz_near {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x y : ℂ} (hx : R+2 < ‖x‖)
    (hxy : ‖x-y‖ ≤ 1) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ (2*M)*‖x-y‖ := by
  have ho : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hb : Metric.closedBall x 1 ⊆ {z : ℂ | R+1 < ‖z‖} :=
    closedBall_subset_exterior (by linarith)
  have hbx : x ∈ Metric.closedBall x 1 := Metric.mem_closedBall_self (by norm_num)
  have hby : y ∈ Metric.closedBall x 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hxy
  have ha (z : ℂ) (hz : z ∈ Metric.closedBall x 1) : DifferentiableAt ℂ f z :=
    hd.differentiableAt (ho.mem_nhds (by have hh : R+1 < ‖z‖ := hb hz; change R < ‖z‖; linarith))
  rw [real_fderiv_sub_norm_eq_deriv (ha x hbx) (ha y hby)]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hd.deriv ho).differentiableAt
      (ho.mem_nhds (by have hh : R+1 < ‖z‖ := hb hz; change R < ‖z‖; linarith)))
    (fun z hz => holomorphic_exterior_secondDeriv_bound hd hM (hb hz))
    (convex_closedBall x (1:ℝ)) hby hbx
  exact h

theorem global_holder_fderiv_of_holomorphic_exterior {f : ℂ → E} {R M : ℝ}
    (hf : ContDiff ℝ 1 f) (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M)
    (hlocal : ∀ S : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ C*‖x-y‖^((1:ℝ)/3)) :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ B) ∧
      ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*‖x-y‖^((1:ℝ)/3) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have ho : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:ℂ) (R+1)).exists_bound_of_continuousOn hDf.continuousOn
  let B := max D M
  have hB0 : 0 ≤ B := hM0.trans (le_max_right _ _)
  have hB (x : ℂ) : ‖fderiv ℝ f x‖ ≤ B := by
    by_cases hx : ‖x‖ ≤ R+1
    · exact (hD x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)).trans
        (le_max_left _ _)
    · have hx' : R+1 < ‖x‖ := lt_of_not_ge hx
      rw [real_fderiv_norm_eq_deriv (hd.differentiableAt
        (ho.mem_nhds (show R < ‖x‖ by linarith)))]
      exact (holomorphic_exterior_deriv_bound hd hM hx').trans (le_max_right _ _)
  obtain ⟨C,hC0,hC⟩ := hlocal (R+3)
  let K := C+2*B+2*M
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hKB : 2*B ≤ K := by dsimp [K]; linarith
  have hKM : 2*M ≤ K := by dsimp [K]; linarith
  refine ⟨B,K,hB0,hC0.trans hKC,hB,?_⟩
  intro x y
  have hp : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hxy : ‖x-y‖ ≤ 1
  · by_cases hx : ‖x‖ ≤ R+2
    · have hy : ‖y‖ ≤ R+3 := by
        have ht : ‖y‖ ≤ ‖x‖+‖x-y‖ := by simpa only [norm_sub_rev] using norm_le_insert' y x
        linarith
      exact (hC x (by simp only [Metric.mem_closedBall,dist_zero_right]; linarith)
        y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)).trans
        (mul_le_mul_of_nonneg_right hKC hp)
    · have hh := holomorphic_exterior_fderiv_lipschitz_near hd hM (lt_of_not_ge hx) hxy
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (norm_nonneg _) hxy (by norm_num : (1:ℝ)/3 ≤ 1))
        (mul_nonneg (by norm_num) hM0)).trans (mul_le_mul_of_nonneg_right hKM hp))
  · have hh : ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ 2*B :=
      (norm_sub_le _ _).trans (by linarith [hB x,hB y])
    have hpow : 1 ≤ ‖x-y‖^((1:ℝ)/3) := Real.one_le_rpow (le_of_not_ge hxy) (by norm_num)
    exact hh.trans ((le_mul_of_one_le_right (mul_nonneg (by norm_num) hB0) hpow).trans
      (mul_le_mul_of_nonneg_right hKB hp))

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem cauchyTransform_apply_swap (g : ℂ → E) (z : ℂ) :
    cauchyTransform g z = (Real.pi:ℂ)⁻¹ • ∫ w : ℂ, (z-w)⁻¹ • g w := by
  rw [cauchyTransform,Pi.smul_apply,convolution_eq_swap]
  rfl

 theorem cauchyTransform_tendsto_zero {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    Tendsto (cauchyTransform g) (cocompact ℂ) (𝓝 0) := by
  have : (cocompact ℂ).IsCountablyGenerated := by
    rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop]
    infer_instance
  have hi : Integrable g := hg.integrable_of_hasCompactSupport hc
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  have hlarge : ∀ᶠ z : ℂ in cocompact ℂ, R+1 ≤ ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (R+1))
  have hi' (z : ℂ) : Integrable (fun w : ℂ => (z-w)⁻¹ • g w) := by
    exact convolutionExistsAt_iff_integrable_swap.mp
      (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
        locallyIntegrable_complex_inv hg z)
  have hb : ∀ᶠ z : ℂ in cocompact ℂ, ∀ᵐ w : ℂ, ‖(z-w)⁻¹ • g w‖ ≤ ‖g w‖ := by
    filter_upwards [hlarge] with z hz
    apply ae_of_all
    intro w
    by_cases hw : w∈tsupport g
    · have hn : 1≤‖z-w‖ := by
        have hh := hR w hw
        have ht := norm_sub_norm_le z w
        linarith
      rw [norm_smul,norm_inv]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hn)
    · simp only [image_eq_zero_of_notMem_tsupport hw,smul_zero,norm_zero,le_refl]
  have hl : ∀ᵐ w : ℂ, Tendsto (fun z : ℂ => (z-w)⁻¹ • g w) (cocompact ℂ) (𝓝 0) := by
    apply ae_of_all
    intro w
    have ht : Tendsto (fun z : ℂ => z-w) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight w).isClosedEmbedding.tendsto_cocompact
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
      rw [←Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    simpa only [Function.comp_def,zero_smul] using (hinv.comp ht).smul_const (g w)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖g w‖)
    (Eventually.of_forall (fun z => (hi' z).aestronglyMeasurable)) hb hi.norm hl
  simp only [integral_zero] at ht
  have he : cauchyTransform g = (fun z => (Real.pi:ℂ)⁻¹ • ∫ w : ℂ, (z-w)⁻¹ • g w) :=
    funext (cauchyTransform_apply_swap g)
  rw [he]
  simpa only [smul_zero] using ht.const_smul (Real.pi:ℂ)⁻¹

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cauchyTransform_holder_holomorphic_off {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) {x : ℂ} (hx : g x=0) :
    DifferentiableAt ℂ (cauchyTransform g) x := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg).differentiable (by simp) x,?_⟩
  have hh := cauchyTransform_holder_complexCurl hg hc hM hH hHg x
  rw [hx,smul_zero] at hh
  exact (sub_eq_zero.mp hh).symm

theorem cauchyTransform_holder_global {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ∃ A B K : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ K ∧
      (∀ x, ‖cauchyTransform g x‖ ≤ A) ∧
      (∀ x, ‖fderiv ℝ (cauchyTransform g) x‖ ≤ B) ∧
      (∀ x y, ‖cauchyTransform g x-cauchyTransform g y‖ ≤ K*‖x-y‖^((1:ℝ)/3)) ∧
      (∀ x y, ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        K*‖x-y‖^((1:ℝ)/3)) := by
  have hf := cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg
  let f0 : ZeroAtInftyContinuousMap ℂ E :=
    ⟨⟨cauchyTransform g,hf.continuous⟩,cauchyTransform_tendsto_zero hg hc⟩
  obtain ⟨A,hA⟩ := f0.isBounded_range.exists_norm_le
  have hA' (x : ℂ) : ‖cauchyTransform g x‖ ≤ A := hA _ ⟨x,rfl⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA' 0)
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  have hd : DifferentiableOn ℂ (cauchyTransform g) {z : ℂ | R < ‖z‖} := by
    intro x hx
    apply (cauchyTransform_holder_holomorphic_off hg hc hM hH hHg ?_).differentiableWithinAt
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hR h
    simp only [Metric.mem_closedBall,dist_zero_right] at hh
    exact (not_le_of_gt hx) hh
  have hlocal (S : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        C*‖x-y‖^((1:ℝ)/3) := by
    obtain ⟨C,hC0,hC⟩ := cauchyTransform_fderiv_holder_on (E := E) (max R S)
    refine ⟨C*H,mul_nonneg hC0 hH,?_⟩
    intro x hx y hy
    exact hC g hg (hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
      M H hM hH hHg x (Metric.closedBall_subset_closedBall (le_max_right _ _) hx)
      y (Metric.closedBall_subset_closedBall (le_max_right _ _) hy)
  obtain ⟨B,K,hB0,hK0,hB,hK⟩ := global_holder_fderiv_of_holomorphic_exterior hf hd hA' hlocal
  have hL : LipschitzWith ⟨B,hB0⟩ (cauchyTransform g) :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun x => hB x)
  refine ⟨A,B,K+B+2*A,hA0,hB0,by positivity,hA',hB,?_,?_⟩
  · intro x y
    have hp : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hxy : ‖x-y‖ ≤ 1
    · have hh : ‖cauchyTransform g x-cauchyTransform g y‖ ≤ B*‖x-y‖ := by
        have ht := hL.dist_le_mul x y
        change dist (cauchyTransform g x) (cauchyTransform g y) ≤ B*dist x y at ht
        simpa only [dist_eq_norm] using ht
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (norm_nonneg _) hxy (by norm_num : (1:ℝ)/3 ≤ 1)) hB0).trans
          (mul_le_mul_of_nonneg_right (by linarith : B ≤ K+B+2*A) hp))
    · have hh : ‖cauchyTransform g x-cauchyTransform g y‖ ≤ 2*A :=
        (norm_sub_le _ _).trans (by linarith [hA' x,hA' y])
      exact hh.trans ((le_mul_of_one_le_right (by positivity : 0 ≤ 2*A)
        (Real.one_le_rpow (le_of_not_ge hxy) (by norm_num : 0 ≤ (1:ℝ)/3))).trans
          (mul_le_mul_of_nonneg_right (by linarith : 2*A ≤ K+B+2*A) hp))
  · intro x y
    exact (hK x y).trans (mul_le_mul_of_nonneg_right (by linarith : K ≤ K+B+2*A)
      (Real.rpow_nonneg (norm_nonneg _) _))

omit [CompleteSpace E] in
lemma integrableKernel_smul_convolution_tendsto {K : ℂ → ℂ} (hK : Integrable K)
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E}
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => MeasureTheory.convolution K (g j) (ContinuousLinearMap.lsmul ℝ ℂ) volume x)
      atTop (𝓝 (MeasureTheory.convolution K v (ContinuousLinearMap.lsmul ℝ ℂ) volume x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖K w‖*M)
  · apply Eventually.of_forall
    intro j
    exact hK.aestronglyMeasurable.smul
      ((hg j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro j
    apply ae_of_all
    intro w
    change ‖K w • g j (x-w)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM j (x-w)) (norm_nonneg _)
  · exact hK.norm.mul_const M
  · apply ae_of_all
    intro w
    exact (hgv (x-w)).const_smul (K w)

omit [CompleteSpace E] in
lemma cauchyTransform_tendsto_compact_data {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w))) {R : ℝ}
    (hgs : ∀ j, tsupport (g j) ⊆ Metric.closedBall (0:ℂ) R)
    (hvs : tsupport v ⊆ Metric.closedBall (0:ℂ) R)
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => cauchyTransform (g j) x) atTop (𝓝 (cauchyTransform v x)) := by
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have he {f : ℂ → E} (hs : tsupport f ⊆ Metric.closedBall (0:ℂ) R) :
      cauchyTransform f x = (Real.pi:ℂ)⁻¹ • MeasureTheory.convolution
        (cutoffCauchyKernel b) f (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
    exact congrArg ((Real.pi:ℂ)⁻¹ • ·) (cutoff_cauchy_supported_eq b (le_refl _)
      (hs.trans (Metric.closedBall_subset_closedBall hRS))
      (show x ∈ Metric.closedBall (0:ℂ) S by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hxS.le)).symm
  simp_rw [he hvs,he (hgs _)]
  exact (integrableKernel_smul_convolution_tendsto (cutoffCauchyKernel_integrableNecessity b)
    hg hgv hM x).const_smul (Real.pi:ℂ)⁻¹

omit [CompleteSpace E] in
lemma cauchyTransform_add_compact {g h : ℂ → E} (hg : Continuous g)
    (hh : Continuous h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    cauchyTransform (g+h) = cauchyTransform g+cauchyTransform h := by
  ext x
  simp only [cauchyTransform_apply,Pi.add_apply,smul_add]
  have hi : Integrable (fun w : ℂ => w⁻¹ • g (x-w)) :=
    hgc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv hg x
  have hi' : Integrable (fun w : ℂ => w⁻¹ • h (x-w)) :=
    hhc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv hh x
  rw [integral_add hi hi',smul_add]

omit [CompleteSpace E] in
lemma cauchyTransform_real_smul (c : ℝ) (g : ℂ → E) :
    cauchyTransform (c • g) = c • cauchyTransform g := by
  ext x
  simp only [cauchyTransform_apply,Pi.smul_apply,smul_comm (n := c),integral_smul]

end

universe u v
variable (K : Type u) [MetricSpace K]

abbrev OffDiagonal := {p : K × K // p.1 ≠ p.2}

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

def holderGraph (α : ℝ) : Submodule ℝ ((K →ᵇ E) × (OffDiagonal K →ᵇ E)) where
  carrier := {p | ∀ z : OffDiagonal K,
    p.1 z.val.1 - p.1 z.val.2 = (dist z.val.1 z.val.2)^α • p.2 z}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq z
    change (p.1 z.val.1+q.1 z.val.1)-(p.1 z.val.2+q.1 z.val.2) = _
    rw [show (p.1 z.val.1+q.1 z.val.1)-(p.1 z.val.2+q.1 z.val.2) =
      (p.1 z.val.1-p.1 z.val.2)+(q.1 z.val.1-q.1 z.val.2) by abel, hp z, hq z]
    exact (smul_add _ _ _).symm
  smul_mem' := by
    intro c p hp z
    change c • p.1 z.val.1-c • p.1 z.val.2 = _
    rw [← smul_sub, hp z, smul_comm]
    rfl

instance holderGraph_isClosed (α : ℝ) : IsClosed (↑(holderGraph K E α) : Set ((K →ᵇ E) × (OffDiagonal K →ᵇ E))) := by
  change IsClosed {p : (K →ᵇ E) × (OffDiagonal K →ᵇ E) | ∀ z : OffDiagonal K,
    p.1 z.val.1 - p.1 z.val.2 = (dist z.val.1 z.val.2)^α • p.2 z}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_eq
    (((BoundedContinuousFunction.evalCLM ℝ z.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ z.val.2).continuous.comp continuous_fst))
    (((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp continuous_snd).const_smul _)

abbrev HolderSpace (α : ℝ) := ↥(holderGraph K E α)

instance holderSpace_complete [CompleteSpace E] (α : ℝ) : CompleteSpace (HolderSpace K E α) :=
  IsClosed.completeSpace_coe

variable {K E}

def holderValue (α : ℝ) : HolderSpace K E α →L[ℝ] (K →ᵇ E) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (holderGraph K E α).subtypeL

def holderDifference (α : ℝ) : HolderSpace K E α →L[ℝ] (OffDiagonal K →ᵇ E) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (holderGraph K E α).subtypeL

@[simp] theorem holderValue_apply (α : ℝ) (f : HolderSpace K E α) (x : K) :
    holderValue α f x = f.val.1 x := rfl

@[simp] theorem holderDifference_apply (α : ℝ) (f : HolderSpace K E α) (z : OffDiagonal K) :
    holderDifference α f z = f.val.2 z := rfl

theorem holderSpace_relation (α : ℝ) (f : HolderSpace K E α) (x y : K) (hxy : x≠y) :
    holderValue α f x - holderValue α f y =
      (dist x y)^α • holderDifference α f ⟨(x,y),hxy⟩ := f.property ⟨(x,y),hxy⟩

theorem holderValue_injective (α : ℝ) : Function.Injective (holderValue (K := K) (E := E) α) := by
  intro f g h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · ext z
    have hf := f.property z
    have hg := g.property z
    have h0 : (dist z.val.1 z.val.2)^α ≠ 0 :=
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne'
    have he : (dist z.val.1 z.val.2)^α • f.val.2 z = (dist z.val.1 z.val.2)^α • g.val.2 z := by
      rw [← hf, ← hg]
      exact congrArg (fun F : K →ᵇ E => F z.val.1-F z.val.2) h
    exact (smul_right_injective E h0) he

theorem holderSpace_estimate (α : ℝ) (hα : 0<α) (f : HolderSpace K E α) (x y : K) :
    ‖holderValue α f x - holderValue α f y‖ ≤ ‖f‖ * (dist x y)^α := by
  by_cases hxy : x=y
  · subst y
    simp [Real.zero_rpow hα.ne']
  rw [holderSpace_relation α f x y hxy, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg dist_nonneg α)]
  have hb : ‖holderDifference α f ⟨(x,y),hxy⟩‖ ≤ ‖f‖ := by
    exact (f.val.2.norm_coe_le_norm _).trans (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg dist_nonneg α)).trans_eq (mul_comm _ _)

def holderSpaceMk (α : ℝ) (f : K →ᵇ E) (H : ℝ) (_hH : 0≤H)
    (hf : ∀ x y : K, ‖f x-f y‖ ≤ H*(dist x y)^α) : HolderSpace K E α := by
  let g : OffDiagonal K →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ((dist z.val.1 z.val.2)^α)⁻¹ • (f z.val.1-f z.val.2))
    (by
      have hd : Continuous (fun z : OffDiagonal K => dist z.val.1 z.val.2) :=
        (continuous_fst.comp continuous_subtype_val).dist
          (continuous_snd.comp continuous_subtype_val)
      have hp : ∀ z : OffDiagonal K, dist z.val.1 z.val.2 ≠ 0 :=
        fun z => dist_ne_zero.mpr z.property
      exact ((hd.rpow_const (fun z => Or.inl (hp z))).inv₀
        (fun z => (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne')).smul
        ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
          (f.continuous.comp (continuous_snd.comp continuous_subtype_val))))
    H (by
      intro z
      have hw : 0<(dist z.val.1 z.val.2)^α := Real.rpow_pos_of_pos (dist_pos.mpr z.property) α
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
      exact (mul_le_mul_of_nonneg_left (hf z.val.1 z.val.2) (inv_nonneg.mpr hw.le)).trans_eq
        (by rw [mul_comm H, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]))
  refine ⟨(f,g),fun z => ?_⟩
  change f z.val.1-f z.val.2 = (dist z.val.1 z.val.2)^α •
    (((dist z.val.1 z.val.2)^α)⁻¹ • (f z.val.1-f z.val.2))
  rw [smul_smul, mul_inv_cancel₀ (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne', one_smul]

@[simp] theorem holderValue_mk (α : ℝ) (f : K →ᵇ E) (H : ℝ) (hH : 0≤H)
    (hf : ∀ x y : K, ‖f x-f y‖ ≤ H*(dist x y)^α) :
    holderValue α (holderSpaceMk α f H hH hf) = f := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
