import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ProfileTraceAdd
import OAI.Geometry.SmoothYau.Geometry.PulledGradientNorm
import OAI.Geometry.SmoothYau.Geometry.QuadraticRemainderSecondBound

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace

lemma cutoff_small_product_bound (χ D f J M : ℝ)
    (hχ : 0 ≤ χ) (_hD : 0 ≤ D) (hf : 0 ≤ f) (hfM : f ≤ M)
    (hJ : 0 ≤ J) (hcut : D ≤ J*Real.sqrt χ) :
    (χ+D)*f ≤ χ*f+J*Real.sqrt M*Real.sqrt (χ*f) := by
  have he : Real.sqrt χ*f = Real.sqrt f*Real.sqrt (χ*f) := by
    rw [Real.sqrt_mul hχ]
    calc
      _ = Real.sqrt χ*((Real.sqrt f)^2) := by rw [Real.sq_sqrt hf]
      _ = _ := by ring
  have hh : Real.sqrt χ*f ≤ Real.sqrt M*Real.sqrt (χ*f) := by
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfM) (Real.sqrt_nonneg _)
  calc
    _ ≤ (χ+J*Real.sqrt χ)*f := mul_le_mul_of_nonneg_right (by linarith) hf
    _ = χ*f+J*(Real.sqrt χ*f) := by ring
    _ ≤ χ*f+J*(Real.sqrt M*Real.sqrt (χ*f)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hJ)
    _ = _ := by ring

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem corrugationSecondRemainder_small_product
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχn : ∀ x, 0 ≤ χ x)
    (f : V → ℝ) (M : ℝ) (hfn : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (hDf : ∀ z, ‖fderiv ℝ F z‖ ≤ f z)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
        C * (χ x*f (N • y x)+Real.sqrt (χ x*f (N • y x))+N⁻¹) := by
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_uniform Γ hΓ hψ hχ hF hy K hK d B hB
  obtain ⟨J,hJ,hcut⟩ := exists_cutoff_sqrt_gradient hχ hχs hχn
  let c := J*Real.sqrt M
  have hc : 0 ≤ c := mul_nonneg hJ.le (Real.sqrt_nonneg _)
  refine ⟨C₀*(1+c),mul_pos hC₀ (by positivity),?_⟩
  intro N hN x hx
  have ht : 0 ≤ χ x*f (N • y x) := mul_nonneg (hχn x) (hfn _)
  have hprod : (χ x+‖fderiv ℝ χ x‖)*f (N • y x) ≤
      χ x*f (N • y x)+c*Real.sqrt (χ x*f (N • y x)) := by
    exact cutoff_small_product_bound _ _ _ _ _ (hχn x) (norm_nonneg _)
      (hfn _) (hfM _) hJ.le (hcut x)
  calc
    _ ≤ C₀*((|χ x|+‖fderiv ℝ χ x‖)*‖fderiv ℝ F (N • y x)‖+N⁻¹) := hrem N hN x hx
    _ ≤ C₀*((χ x+‖fderiv ℝ χ x‖)*f (N • y x)+N⁻¹) := by
      rw [abs_of_nonneg (hχn x)]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (hDf _) (add_nonneg (hχn x) (norm_nonneg _))) le_rfl) hC₀.le
    _ ≤ C₀*(χ x*f (N • y x)+c*Real.sqrt (χ x*f (N • y x))+N⁻¹) := by gcongr
    _ ≤ C₀*(1+c)*(χ x*f (N • y x)+Real.sqrt (χ x*f (N • y x))+N⁻¹) := by
      have h1 := mul_nonneg hc ht
      have h2 := mul_nonneg hc (inv_nonneg.mpr hN.le)
      have hs := Real.sqrt_nonneg (χ x*f (N • y x))
      nlinarith only [h1,h2,hs,hC₀]

theorem corrugationSecondRemainder_small_product_scaled
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχn : ∀ x, 0 ≤ χ x)
    (f : V → ℝ) (M Jf : ℝ) (hJf : 0 ≤ Jf)
    (hfn : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (hDf : ∀ z, ‖fderiv ℝ F z‖ ≤ Jf*f z)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
        C * (χ x*f (N • y x)+Real.sqrt (χ x*f (N • y x))+N⁻¹) := by
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_uniform Γ hΓ hψ hχ hF hy K hK d B hB
  obtain ⟨J,hJ,hcut⟩ := exists_cutoff_sqrt_gradient hχ hχs hχn
  let c := J*Real.sqrt M
  have hc : 0 ≤ c := mul_nonneg hJ.le (Real.sqrt_nonneg _)
  refine ⟨C₀*(1+Jf)*(1+c),by positivity,?_⟩
  intro N hN x hx
  have ht : 0 ≤ χ x*f (N • y x) := mul_nonneg (hχn x) (hfn _)
  have hs := Real.sqrt_nonneg (χ x*f (N • y x))
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hprod : (χ x+‖fderiv ℝ χ x‖)*f (N • y x) ≤
      χ x*f (N • y x)+c*Real.sqrt (χ x*f (N • y x)) :=
    cutoff_small_product_bound _ _ _ _ _ (hχn x) (norm_nonneg _) (hfn _) (hfM _) hJ.le (hcut x)
  calc
    _ ≤ C₀*((|χ x|+‖fderiv ℝ χ x‖)*‖fderiv ℝ F (N • y x)‖+N⁻¹) := hrem N hN x hx
    _ ≤ C₀*((χ x+‖fderiv ℝ χ x‖)*(Jf*f (N • y x))+N⁻¹) := by
      rw [abs_of_nonneg (hχn x)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hDf _)
          (add_nonneg (hχn x) (norm_nonneg _))) le_rfl) hC₀.le
    _ = C₀*(Jf*((χ x+‖fderiv ℝ χ x‖)*f (N • y x))+N⁻¹) := by ring
    _ ≤ C₀*(Jf*(χ x*f (N • y x)+c*Real.sqrt (χ x*f (N • y x)))+N⁻¹) := by gcongr
    _ ≤ C₀*((1+Jf)*(1+c)*(χ x*f (N • y x)+Real.sqrt (χ x*f (N • y x))+N⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      have h1 := mul_nonneg hJf ht
      have h2 := mul_nonneg hc ht
      have h3 := mul_nonneg hJf hs
      have h4 := mul_nonneg hJf hNi
      have h5 := mul_nonneg hc hNi
      have h6 := mul_nonneg (mul_nonneg hJf hc) ht
      have h7 := mul_nonneg (mul_nonneg hJf hc) hNi
      have h8 := mul_nonneg hc hs
      nlinarith only [ht,hs,h1,h2,h3,h4,h5,h6,h7,h8]
    _ = _ := by ring


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_radialCorrugation_strict
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (hβv : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmallR : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (Fmax K S : ℝ) (hFmax : 0 ≤ Fmax) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ K)
    (m α M Hmax δ A : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (haM : ∀ x, ‖pulledGradient (j x) ψ x‖ ≤ M)
    (hHH : ∀ x, ‖pulledHessian Γ (j x) ψ x‖ ≤ Hmax)
    (hAa : ∀ x, A ≤ 2*‖pulledGradient (j x) ψ x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (pulledGradient (j x) ψ x) w = 0 →
      m ≤ profileTrace (pulledHessian Γ (j x) ψ x) (pulledGradient (j x) ψ x) w)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : K₀,
      profileStrict (pulledHessian Γ (j x) (radialCorrugation ψ χ y β b δ A N) x)
        (pulledGradient (j x) (radialCorrugation ψ χ y β b δ A N) x) ∧
      pulledGradient (j x) (radialCorrugation ψ χ y β b δ A N) x ≠ 0 := by
  let F := periodicRadialFunction β b
  have hF : ContDiff ℝ ∞ F := radial_periodic_smooth hβ hr hb hzero
  obtain ⟨B₀,hB₀,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmallR hb hzero
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  let Ce := |δ*A| *B₀*D'*J
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_small_product_scaled Γ hΓ hψ hχ hF hy hχs
    (fun x => (hχv x).1) (periodicRadialSpeed β R) Fmax 2 (by norm_num)
    (fun z => (hcoef z).1) (fun z => (hcoef z).2.1)
    (periodicRadialFunction_fderiv_bound hβ hβ0 (fun t => (hβv t).1) hr hrR hsmallR hb hzero)
    K₀ hK₀ (δ*A) B₀ hBF
  let Cr := C₀*J^2
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  let a : ∀ x, V x := fun x => pulledGradient (j x) ψ x
  let H : ∀ x, ProfileForm (V x) := fun x => pulledHessian Γ (j x) ψ x
  let z : ℕ → K₀ → ProfilePlane := fun N x => periodicRadialOffset R ((N:ℝ) • y x)
  let D₁ : ∀ x, V x →L[ℝ] ProfilePlane := fun x => (fderiv ℝ y x).comp (j x)
  let R₁ : ℕ → ∀ x, V x →L[ℝ] ℝ := fun N x => (planeRadialCovector (z N x)).comp (D₁ x)
  let T₁ : ℕ → ∀ x, V x →L[ℝ] ℝ := fun N x => (planeAngularCovector (z N x)).comp (D₁ x)
  let r₁ : ℕ → ∀ x, V x := fun N x => (InnerProductSpace.toDual ℝ (V x)).symm (R₁ N x)
  let e : ℕ → ∀ x, V x := fun N x => (δ*A/(N:ℝ)*F ((N:ℝ) • y x)) • pulledGradient (j x) χ x
  let f : ℕ → K₀ → ℝ := fun N x => periodicRadialSpeed β R ((N:ℝ) • y x)
  let b₁ : ℕ → K₀ → ℝ := fun N x => periodicAngularSecond β R ((N:ℝ) • y x)
  let f₂ : ℕ → K₀ → ℝ := fun N x => periodicRadialSecond β R ((N:ℝ) • y x)
  let B : ℕ → ∀ x, ProfileForm (V x) := fun N x => pulledRadialLeading (j x) y β b N x
  let Er : ℕ → ∀ x, ProfileForm (V x) := fun N x => pulledRadialRemainder Γ (j x) ψ χ y β b δ A N x
  have hR : 0 < R := hr.trans_lt hrR
  have hframes (N : ℕ) (x : K₀) := radial_coframe_bounds (D₁ x) (a x) (z N x) (hfirst x) (hup x) (hlo x)
  have hnat : ∀ᶠ N : ℕ in atTop, 0 < (N:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact_mod_cast hN
  have he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ) := by
    filter_upwards [hnat] with N hN x
    have hg : ‖pulledGradient (j x) χ x‖ ≤ D'*J :=
      (pulledGradient_norm_le (j x) χ x).trans (mul_le_mul
        ((hD x x.property).trans (le_max_left _ _)) (hj x) (norm_nonneg _) hD')
    dsimp only [e,Ce]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hN]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B₀)*(D'*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hN.le)) hg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹) := by
    filter_upwards [hnat] with N hN x
    have ht : 0 ≤ χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹ := by
      have hf : 0 ≤ f N x := (hcoef _).1
      have hχn : 0 ≤ χ x := (hχv x).1
      positivity
    calc
      _ ≤ ‖corrugationSecondRemainder Γ ψ χ F y (δ*A) N x‖*‖j x‖^2 :=
        norm_bilinear_pullback_le _ _
      _ ≤ (C₀*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹))*J^2 :=
        mul_le_mul (hrem N hN x x.property) (sq_le_sq₀ (norm_nonneg _) hJ |>.mpr (hj x))
          (sq_nonneg _) (mul_nonneg hC₀.le ht)
      _ = _ := by dsimp [Cr]; ring
  have hs := radial_uniform_strict_bundle hd a H (fun x => χ x) r₁ e R₁ T₁ f b₁ f₂ B Er
    m α M Hmax δ A K S (2*R) Fmax Ce Cr hm hm1 hα hM hHmax hδ hA hK hS
    (by positivity) hFmax hCe hCr hsmall ha0 haM hHH hAa hmargin (fun x => hχv x)
    (fun N x => ⟨(hcoef _).1,(hcoef _).2.1⟩)
    (fun N x => periodicRadialSpeed_le_angular (fun t => (hβv t).1) hR _)
    (fun N x => (hcoef _).2.2.1) (fun N x => (hcoef _).2.2.2)
    (fun N x v => InnerProductSpace.toDual_symm_apply)
    (fun N x => (hframes N x).1) (fun N x => (hframes N x).2.1)
    (fun N x => (hframes N x).2.2.1) (fun N x => (hframes N x).2.2.2)
    (fun N x v w => pulledRadialLeading_decomposition (j x) y hβ hβ0 hr hrR hsmallR hb hzero N x v w)
    he hEr
  filter_upwards [hs,hnat] with N hsN hN x
  rw [radialCorrugation_hessian,radialCorrugation_gradient hψ hχ hy hβ hβ0 hr hrR hsmallR hb hzero
    (j x) δ A N (ne_of_gt hN)]
  exact hsN x



end YauCounterexamples
end

end OAI
