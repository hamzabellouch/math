import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoordinateCovariantSecondAddConst

namespace OAI

noncomputable section
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
namespace YauCounterexamples
open Set Filter
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coframe_radial_norm_lower (hd : 3 ≤ Module.finrank ℝ E)
    (a : E) (R T : E →L[ℝ] ℝ)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2)) :
    (1:ℝ)/2 ≤ ‖(InnerProductSpace.toDual ℝ E).symm R‖ := by
  obtain ⟨v,hv,hav,hTv⟩ := exists_unit_common_kernel hd (InnerProductSpace.toDual ℝ E a) T
  have hh := hco v hav
  rw [hv,hTv,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] at hh
  have hi := abs_real_inner_le_norm ((InnerProductSpace.toDual ℝ E).symm R) v
  rw [InnerProductSpace.toDual_symm_apply,hv,mul_one] at hi
  exact hh.trans hi

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialCorrugation_support (ψ χ : E → ℝ) (y : E → ProfilePlane)
    (β : ℝ → ℝ) (b δ A N : ℝ) :
    tsupport (fun x => radialCorrugation ψ χ y β b δ A N x-ψ x) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp [radialCorrugation,hx]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialCorrugation_uniform_C0 {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0) (δ A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x, |radialCorrugation ψ χ y β b δ A N x-ψ x| < ε := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  have hn : Tendsto (fun N : ℕ => |δ*A| * B/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with N hNε hN x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hχb : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχ x).1]; exact (hχ x).2
  have ht : |χ x*periodicRadialFunction β b ((N:ℝ) • y x)| ≤ B := by
    rw [abs_mul]
    calc
      _ ≤ 1*B := mul_le_mul hχb (hBF _) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  dsimp only [radialCorrugation]
  rw [add_sub_cancel_left,abs_mul,abs_div,abs_of_pos hNp]
  exact (mul_le_mul_of_nonneg_left ht (div_nonneg (abs_nonneg _) hNp.le)).trans_lt
    (by simpa only [div_mul_eq_mul_div] using hNε)

omit [FiniteDimensional ℝ E] in
theorem actual_radialCorrugation_gain
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (α δ A c ε : ℝ) (hα : 0 < α) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hε : 0 < ε) (hε1 : ε < 1)
    (ha : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (hA : ∀ x, ‖pulledGradient (j x) ψ x‖/2 ≤ A)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : K₀,
      pulledGradient (j x) (radialCorrugation ψ χ y β b δ A N) x ≠ 0 ∧
      (1-ε)*‖pulledGradient (j x) ψ x‖ ≤
        ‖pulledGradient (j x) (radialCorrugation ψ χ y β b δ A N) x‖ ∧
      (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • y x) →
        (Real.sqrt (1+δ^2*c^2/16)-ε)*‖pulledGradient (j x) ψ x‖ ≤
          ‖pulledGradient (j x) (radialCorrugation ψ χ y β b δ A N) x‖) := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let C := |δ*A| * B*(max D 0)*J
  have hn : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds (mul_pos hε hα)),eventually_gt_atTop (0:ℕ)] with N hCN hN x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let a := pulledGradient (j x) ψ x
  let z := periodicRadialOffset R ((N:ℝ) • y x)
  let D₁ := (fderiv ℝ y x).comp (j x)
  let R₁ := (planeRadialCovector z).comp D₁
  let T₁ := (planeAngularCovector z).comp D₁
  let r₁ := (InnerProductSpace.toDual ℝ (V x)).symm R₁
  let e := (δ*A/(N:ℝ)*periodicRadialFunction β b ((N:ℝ) • y x)) • pulledGradient (j x) χ x
  let f := periodicRadialSpeed β R ((N:ℝ) • y x)
  have hframes := radial_coframe_bounds D₁ a z (hfirst x) (hup x) (hlo x)
  have har : inner ℝ a r₁ = 0 := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply.trans hframes.1
  have hre : (1:ℝ)/2 ≤ ‖r₁‖ := coframe_radial_norm_lower (hd x) a R₁ T₁ hframes.2.2.2
  have heg : ‖pulledGradient (j x) χ x‖ ≤ max D 0*J :=
    (pulledGradient_norm_le (j x) χ x).trans <|
      (mul_le_mul_of_nonneg_left (hj x) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right ((hD x x.property).trans (le_max_left _ _)) hJ)
  have heC : ‖e‖ ≤ C/(N:ℝ) := by
    dsimp only [e,C]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hNp]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B)*(max D 0*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hNp.le)) heg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have he : ‖e‖ ≤ ε*‖a‖ := heC.trans (hCN.le.trans (mul_le_mul_of_nonneg_left (ha x) hε.le))
  have heq := radialCorrugation_gradient hψ hχ hy hβ hβ0 hr hrR hsmall hb hz (j x) δ A N hNp.ne' x
  rw [heq]
  change a+(δ*A*χ x*f) • r₁+e ≠ 0 ∧ _
  have hnl := radial_gradient_no_loss a r₁ e har (δ*A*χ x*f) ε he
  refine ⟨norm_pos_iff.mp ((mul_pos (sub_pos.mpr hε1) (hα.trans_le (ha x))).trans_le hnl),hnl,?_⟩
  intro hχx hfx
  rw [hχx,mul_one]
  exact radial_gradient_annular_gain a r₁ e har δ A f c ε hδ hc hfx (hA x) hre he

end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_radialCorrugation_strict_shift
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
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
      profileStrict (pulledHessian Γ (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x)
        (pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x) ∧
      pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x ≠ 0 := by
  let F := periodicRadialFunction β b
  have hF : ContDiff ℝ ∞ F := radial_periodic_smooth hβ hr hb hzero
  obtain ⟨B₀,hB₀,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmallR hb hzero
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  let Ce := |δ*A| *B₀*D'*J
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_small_product_scaled_shift Γ hΓ hψ hχ hF hy hχs
    (fun x => (hχv x).1) (periodicRadialSpeed β R) Fmax 2 (by norm_num)
    (fun z => (hcoef z).1) (fun z => (hcoef z).2.1)
    (periodicRadialFunction_fderiv_bound hβ hβ0 (fun t => (hβv t).1) hr hrR hsmallR hb hzero)
    K₀ hK₀ (δ*A) B₀ hBF
  let Cr := C₀*J^2
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  let X := K₀ × ProfilePlane
  let a : ∀ x : X, V x.1 := fun x => pulledGradient (j x.1) ψ x.1
  let H : ∀ x : X, ProfileForm (V x.1) := fun x => pulledHessian Γ (j x.1) ψ x.1
  let z : ℕ → X → ProfilePlane := fun N x => periodicRadialOffset R ((N:ℝ) • (y x.1+x.2))
  let D₁ : ∀ x : X, V x.1 →L[ℝ] ProfilePlane := fun x => (fderiv ℝ y x.1).comp (j x.1)
  let R₁ : ℕ → ∀ x : X, V x.1 →L[ℝ] ℝ := fun N x => (planeRadialCovector (z N x)).comp (D₁ x)
  let T₁ : ℕ → ∀ x : X, V x.1 →L[ℝ] ℝ := fun N x => (planeAngularCovector (z N x)).comp (D₁ x)
  let r₁ : ℕ → ∀ x : X, V x.1 := fun N x => (InnerProductSpace.toDual ℝ (V x.1)).symm (R₁ N x)
  let e : ℕ → ∀ x : X, V x.1 := fun N x => (δ*A/(N:ℝ)*F ((N:ℝ) • (y x.1+x.2))) • pulledGradient (j x.1) χ x.1
  let f : ℕ → X → ℝ := fun N x => periodicRadialSpeed β R ((N:ℝ) • (y x.1+x.2))
  let b₁ : ℕ → X → ℝ := fun N x => periodicAngularSecond β R ((N:ℝ) • (y x.1+x.2))
  let f₂ : ℕ → X → ℝ := fun N x => periodicRadialSecond β R ((N:ℝ) • (y x.1+x.2))
  let B : ℕ → ∀ x : X, ProfileForm (V x.1) := fun N x => pulledRadialLeading (j x.1) (fun t => y t+x.2) β b N x.1
  let Er : ℕ → ∀ x : X, ProfileForm (V x.1) := fun N x => pulledRadialRemainder Γ (j x.1) ψ χ (fun t => y t+x.2) β b δ A N x.1
  have hR : 0 < R := hr.trans_lt hrR
  have hframes (N : ℕ) (x : X) := radial_coframe_bounds (D₁ x) (a x) (z N x) (hfirst x.1) (hup x.1) (hlo x.1)
  have hnat : ∀ᶠ N : ℕ in atTop, 0 < (N:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact_mod_cast hN
  have he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ) := by
    filter_upwards [hnat] with N hN x
    have hg : ‖pulledGradient (j x.1) χ x.1‖ ≤ D'*J :=
      (pulledGradient_norm_le (j x.1) χ x.1).trans (mul_le_mul
        ((hD x.1 x.1.property).trans (le_max_left _ _)) (hj x.1) (norm_nonneg _) hD')
    dsimp only [e,Ce]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hN]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B₀)*(D'*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hN.le)) hg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹) := by
    filter_upwards [hnat] with N hN x
    have ht : 0 ≤ χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹ := by
      have hf : 0 ≤ f N x := (hcoef _).1
      have hχn : 0 ≤ χ x.1 := (hχv x.1).1
      positivity
    calc
      _ ≤ ‖corrugationSecondRemainder Γ ψ χ F (fun t => y t+x.2) (δ*A) N x.1‖*‖j x.1‖^2 :=
        norm_bilinear_pullback_le _ _
      _ ≤ (C₀*(χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹))*J^2 :=
        mul_le_mul (hrem N hN x.2 x.1 x.1.property) (sq_le_sq₀ (norm_nonneg _) hJ |>.mpr (hj x.1))
          (sq_nonneg _) (mul_nonneg hC₀.le ht)
      _ = _ := by dsimp [Cr]; ring
  have hs := radial_uniform_strict_bundle (fun x : X => hd x.1) a H (fun x => χ x.1) r₁ e R₁ T₁ f b₁ f₂ B Er
    m α M Hmax δ A K S (2*R) Fmax Ce Cr hm hm1 hα hM hHmax hδ hA hK hS
    (by positivity) hFmax hCe hCr hsmall
    (fun x => ha0 x.1) (fun x => haM x.1) (fun x => hHH x.1) (fun x => hAa x.1)
    (fun x => hmargin x.1) (fun x => hχv x.1)
    (fun N x => ⟨(hcoef _).1,(hcoef _).2.1⟩)
    (fun N x => periodicRadialSpeed_le_angular (fun t => (hβv t).1) hR _)
    (fun N x => (hcoef _).2.2.1) (fun N x => (hcoef _).2.2.2)
    (fun N x v => InnerProductSpace.toDual_symm_apply)
    (fun N x => (hframes N x).1) (fun N x => (hframes N x).2.1)
    (fun N x => (hframes N x).2.2.1) (fun N x => (hframes N x).2.2.2)
    (fun N x v w => by
      simpa only [B,f₂,b₁,R₁,T₁,z,D₁,ContinuousLinearMap.comp_apply,fderiv_add_const] using pulledRadialLeading_decomposition (j x.1) (fun t => y t+x.2)
        hβ hβ0 hr hrR hsmallR hb hzero N x.1 v w)
    he hEr
  filter_upwards [hs,hnat] with N hsN hN d x
  rw [radialCorrugation_hessian,radialCorrugation_gradient hψ hχ (hy.add contDiff_const)
    hβ hβ0 hr hrR hsmallR hb hzero (j x) δ A N (ne_of_gt hN)]
  simpa only [fderiv_add_const] using hsN (x,d)

omit [FiniteDimensional ℝ E] in
theorem actual_radialCorrugation_gain_shift
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (α δ A c ε : ℝ) (hα : 0 < α) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hε : 0 < ε) (hε1 : ε < 1)
    (ha : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (hA : ∀ x, ‖pulledGradient (j x) ψ x‖/2 ≤ A)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
      pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x ≠ 0 ∧
      (1-ε)*‖pulledGradient (j x) ψ x‖ ≤
        ‖pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x‖ ∧
      (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y x+d)) →
        (Real.sqrt (1+δ^2*c^2/16)-ε)*‖pulledGradient (j x) ψ x‖ ≤
          ‖pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x‖) := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let C := |δ*A| * B*(max D 0)*J
  have hn : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds (mul_pos hε hα)),eventually_gt_atTop (0:ℕ)] with N hCN hN d x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let a := pulledGradient (j x) ψ x
  let z := periodicRadialOffset R ((N:ℝ) • (y x+d))
  let D₁ := (fderiv ℝ y x).comp (j x)
  let R₁ := (planeRadialCovector z).comp D₁
  let T₁ := (planeAngularCovector z).comp D₁
  let r₁ := (InnerProductSpace.toDual ℝ (V x)).symm R₁
  let e := (δ*A/(N:ℝ)*periodicRadialFunction β b ((N:ℝ) • (y x+d))) • pulledGradient (j x) χ x
  let f := periodicRadialSpeed β R ((N:ℝ) • (y x+d))
  have hframes := radial_coframe_bounds D₁ a z (hfirst x) (hup x) (hlo x)
  have har : inner ℝ a r₁ = 0 := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply.trans hframes.1
  have hre : (1:ℝ)/2 ≤ ‖r₁‖ := coframe_radial_norm_lower (hd x) a R₁ T₁ hframes.2.2.2
  have heg : ‖pulledGradient (j x) χ x‖ ≤ max D 0*J :=
    (pulledGradient_norm_le (j x) χ x).trans <|
      (mul_le_mul_of_nonneg_left (hj x) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right ((hD x x.property).trans (le_max_left _ _)) hJ)
  have heC : ‖e‖ ≤ C/(N:ℝ) := by
    dsimp only [e,C]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hNp]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B)*(max D 0*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hNp.le)) heg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have he : ‖e‖ ≤ ε*‖a‖ := heC.trans (hCN.le.trans (mul_le_mul_of_nonneg_left (ha x) hε.le))
  have heq := radialCorrugation_gradient hψ hχ (hy.add (contDiff_const (c:=d))) hβ hβ0 hr hrR hsmall hb hz (j x) δ A N hNp.ne' x
  simp only [fderiv_add_const] at heq
  rw [heq]
  change a+(δ*A*χ x*f) • r₁+e ≠ 0 ∧ _
  have hnl := radial_gradient_no_loss a r₁ e har (δ*A*χ x*f) ε he
  refine ⟨norm_pos_iff.mp ((mul_pos (sub_pos.mpr hε1) (hα.trans_le (ha x))).trans_le hnl),hnl,?_⟩
  intro hχx hfx
  rw [hχx,mul_one]
  exact radial_gradient_annular_gain a r₁ e har δ A f c ε hδ hc hfx (hA x) hre he

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialCorrugation_uniform_C0_shift {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0) (δ A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x, |radialCorrugation ψ χ (fun t => y t+d) β b δ A N x-ψ x| < ε := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  have hn : Tendsto (fun N : ℕ => |δ*A| * B/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with N hNε hN d x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hχb : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχ x).1]; exact (hχ x).2
  have ht : |χ x*periodicRadialFunction β b ((N:ℝ) • (y x+d))| ≤ B := by
    rw [abs_mul]
    calc
      _ ≤ 1*B := mul_le_mul hχb (hBF _) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  dsimp only [radialCorrugation]
  rw [add_sub_cancel_left,abs_mul,abs_div,abs_of_pos hNp]
  exact (mul_le_mul_of_nonneg_left ht (div_nonneg (abs_nonneg _) hNp.le)).trans_lt
    (by simpa only [div_mul_eq_mul_div] using hNε)

end
end YauCounterexamples

end OAI
