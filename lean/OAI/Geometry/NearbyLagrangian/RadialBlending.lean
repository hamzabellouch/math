import Mathlib

namespace OAI

/-! Radial interpolation without new critical points outside a bounded set. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.InfinityRestore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def blend (α F G : E → ℝ) (x : E) : ℝ := (1 - α x) * F x + α x * G x

lemma fderiv_blend {α F G : E → ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (blend α F G) x =
      (1 - α x) • fderiv ℝ F x + α x • fderiv ℝ G x +
        (G x - F x) • fderiv ℝ α x := by
  have h := ((hasFDerivAt_const (1 : ℝ) x).sub hα.hasFDerivAt).mul hF.hasFDerivAt
  have h' := h.add (hα.hasFDerivAt.mul hG.hasFDerivAt)
  change HasFDerivAt (blend α F G) _ x at h'
  rw [h'.fderiv]
  ext z
  simp only [add_apply, sub_apply, smul_apply, zero_apply, smul_eq_mul, Pi.sub_apply]
  ring

lemma norm_fderiv_blend_sub_le {α F G : E → ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (ha : α x ∈ Icc 0 1)
    {D₀ : E →L[ℝ] ℝ} {εF εG εv B : ℝ}
    (hεF : ‖fderiv ℝ F x - D₀‖ ≤ εF)
    (hεG : ‖fderiv ℝ G x - D₀‖ ≤ εG)
    (hεv : |G x - F x| ≤ εv) (hB : ‖fderiv ℝ α x‖ ≤ B) :
    ‖fderiv ℝ (blend α F G) x - D₀‖ ≤ εF + εG + εv * B := by
  have ha0 := ha.1
  have ha1 := ha.2
  have heF : 0 ≤ εF := (norm_nonneg _).trans hεF
  have heG : 0 ≤ εG := (norm_nonneg _).trans hεG
  have hev : 0 ≤ εv := (abs_nonneg _).trans hεv
  have hBB : 0 ≤ B := (norm_nonneg _).trans hB
  have heq : fderiv ℝ (blend α F G) x - D₀ =
      (1 - α x) • (fderiv ℝ F x - D₀) + α x • (fderiv ℝ G x - D₀) +
        (G x - F x) • fderiv ℝ α x := by
    rw [fderiv_blend hα hF hG]
    ext z
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖(1 - α x) • (fderiv ℝ F x - D₀)‖ +
        ‖α x • (fderiv ℝ G x - D₀)‖ + ‖(G x - F x) • fderiv ℝ α x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1 - α x) * ‖fderiv ℝ F x - D₀‖ + α x * ‖fderiv ℝ G x - D₀‖ +
        |G x - F x| * ‖fderiv ℝ α x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1,
        abs_of_nonneg (sub_nonneg.mpr ha.2)]
    _ ≤ (1 - α x) * εF + α x * εG + εv * B := by
      gcongr
    _ ≤ εF + εG + εv * B := by nlinarith

lemma fderiv_ne_zero_of_error_lt {F : E → ℝ} {x : E} {D₀ : E →L[ℝ] ℝ}
    {r ε : ℝ} (h₀ : r ≤ ‖D₀‖) (hd : ‖fderiv ℝ F x - D₀‖ ≤ ε)
    (hε : ε < r) : fderiv ℝ F x ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg] at hd
  exact (h₀.trans hd).not_gt hε

variable [HasContDiffBump E]

def unitBump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def radialCutoff (A : ℝ) (x : E) : ℝ := 1 - (unitBump (E := E)) (A⁻¹ • x)

lemma contDiff_radialCutoff (A : ℝ) : ContDiff ℝ ∞ (radialCutoff (E := E) A) :=
  contDiff_const.sub ((unitBump (E := E)).contDiff.comp (contDiff_const.smul contDiff_id))

lemma radialCutoff_mem_Icc (A : ℝ) (x : E) : radialCutoff A x ∈ Icc (0 : ℝ) 1 := by
  have h := show (unitBump (E := E)) (A⁻¹ • x) ∈ Icc (0 : ℝ) 1 from
    ⟨(unitBump (E := E)).nonneg, (unitBump (E := E)).le_one⟩
  constructor <;> dsimp [radialCutoff] <;> linarith [h.1, h.2]

lemma radialCutoff_eq_zero {A : ℝ} (hA : 0 < A) {x : E} (hx : ‖x‖ ≤ A) :
    radialCutoff A x = 0 := by
  apply sub_eq_zero.mpr
  symm
  apply (unitBump (E := E)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hA, unitBump]
  exact (inv_mul_le_iff₀ hA).mpr (by simpa using hx)

lemma radialCutoff_eq_one {A : ℝ} (hA : 0 < A) {x : E} (hx : 2 * A ≤ ‖x‖) :
    radialCutoff A x = 1 := by
  have hb : (unitBump (E := E)) (A⁻¹ • x) = 0 := by
    apply (unitBump (E := E)).zero_of_le_dist
    simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hA,
      unitBump]
    exact (le_inv_mul_iff₀ hA).mpr (by nlinarith)
  simp [radialCutoff, hb]

variable [FiniteDimensional ℝ E]

lemma exists_unitBump_derivative_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ B := by
  have hc : Continuous (fderiv ℝ (unitBump (E := E))) :=
    (unitBump (E := E)).contDiff (n := 1) |>.continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ (unitBump (E := E))) :=
    (unitBump (E := E)).hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

omit [FiniteDimensional ℝ E] in
lemma norm_fderiv_radialCutoff_le {B A : ℝ} (hA : 0 < A)
    (hB : ∀ x : E, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ B) (x : E) :
    ‖fderiv ℝ (radialCutoff A) x‖ ≤ B / A := by
  have hd := ((unitBump (E := E)).contDiff (n := 1) |>.differentiable (by simp)
      (A⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul A⁻¹)
  have h := (hasFDerivAt_const (1 : ℝ) x).sub hd
  change HasFDerivAt (radialCutoff A) _ x at h
  rw [h.fderiv]
  simp only [zero_sub, norm_neg]
  calc
    _ ≤ ‖fderiv ℝ (unitBump (E := E)) (A⁻¹ • x)‖ * ‖A⁻¹ • ContinuousLinearMap.id ℝ E‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * A⁻¹ := by
      have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hA]
      exact mul_le_mul (hB _) (by nlinarith [inv_pos.mpr hA])
        (mul_nonneg (inv_nonneg.mpr hA.le) (norm_nonneg _)) ((norm_nonneg _).trans (hB (A⁻¹ • x)))
    _ = B / A := by rw [div_eq_mul_inv]

end NearbyLagrangian.InfinityRestore

namespace NearbyLagrangian.InfinityRestore

open scoped ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E]

lemma blend_radial_eq_inner {A : ℝ} (hA : 0 < A) (F G : E → ℝ) {x : E}
    (hx : ‖x‖ ≤ A) : blend (radialCutoff A) F G x = F x := by
  simp [blend, radialCutoff_eq_zero hA hx]

lemma blend_radial_eq_outer {A : ℝ} (hA : 0 < A) (F G : E → ℝ) {x : E}
    (hx : 2*A ≤ ‖x‖) : blend (radialCutoff A) F G x = G x := by
  simp [blend, radialCutoff_eq_one hA hx]

lemma blend_radial_inner_eventuallyEq {A : ℝ} (hA : 0 < A) (F G : E → ℝ) {x : E}
    (hx : ‖x‖ < A) : blend (radialCutoff A) F G =ᶠ[𝓝 x] F := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
  exact blend_radial_eq_inner hA F G hy.le

lemma blend_radial_outer_eventuallyEq {A : ℝ} (hA : 0 < A) (F G : E → ℝ) {x : E}
    (hx : 2*A < ‖x‖) : blend (radialCutoff A) F G =ᶠ[𝓝 x] G := by
  filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
  exact blend_radial_eq_outer hA F G hy.le

lemma contDiff_blend_radial {A : ℝ} (hA : 0 < A) {F G : E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ∀ x ≠ 0, ContDiffAt ℝ ∞ G x) :
    ContDiff ℝ ∞ (blend (radialCutoff A) F G) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · apply hF.contDiffAt.congr_of_eventuallyEq
    exact blend_radial_inner_eventuallyEq hA F G (by simpa [hx] using hA)
  · exact (contDiffAt_const.sub (contDiff_radialCutoff A).contDiffAt).mul hF.contDiffAt |>.add
      ((contDiff_radialCutoff A).contDiffAt.mul (hG x hx))

omit [HasContDiffBump E] in

lemma critical_radius_bound {F G₀ : E → ℝ} {c M₁ : ℝ} (hc : 0 < c)
    (h₀ : ∀ x, c*‖x‖ ≤ ‖fderiv ℝ G₀ x‖)
    (h₁ : ∀ x, ‖fderiv ℝ F x - fderiv ℝ G₀ x‖ ≤ M₁)
    {x : E} (hx : fderiv ℝ F x = 0) : ‖x‖ ≤ M₁/c := by
  have h := h₁ x
  rw [hx, zero_sub, norm_neg] at h
  exact (le_div_iff₀ hc).mpr (by nlinarith [h₀ x])

lemma annulus_error_estimate {A r M₀ M₁ B e d : ℝ}
    (hA : 1 ≤ A) (hrA : A ≤ r) (hr2A : r ≤ 2*A)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d) :
    M₁ + e*r + (M₀ + d*r^2) * (B/A) ≤
      ((M₁+B*M₀)/A + e + 2*B*d)*r := by
  have hAp : 0 < A := by linarith
  have hrp : 0 ≤ r := by linarith
  have hlin : M₁*A ≤ M₁*r := mul_le_mul_of_nonneg_left hrA hM₁
  have hval : B*M₀ ≤ B*M₀*r := by nlinarith [mul_nonneg hB hM₀]
  have hsq : B*d*r^2 ≤ 2*B*d*A*r := by
    nlinarith [mul_le_mul_of_nonneg_left hr2A (mul_nonneg (mul_nonneg hB hd) hrp)]
  apply (mul_le_mul_iff_of_pos_right hAp).mp
  field_simp
  nlinarith

lemma blend_radial_annulus_noncritical {F G₀ G : E → ℝ}
    {A c M₀ M₁ B e d : ℝ} (hA : 1 ≤ A)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hunit : ∀ x : E, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ B)
    (hscale : (M₁+B*M₀)/A + e + 2*B*d < c)
    {x : E} (hxA : A ≤ ‖x‖) (hx2A : ‖x‖ ≤ 2*A)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (h₀ : c*‖x‖ ≤ ‖fderiv ℝ G₀ x‖)
    (h₁ : ‖fderiv ℝ F x - fderiv ℝ G₀ x‖ ≤ M₁)
    (hg : ‖fderiv ℝ G x - fderiv ℝ G₀ x‖ ≤ e*‖x‖)
    (hv : |G x - F x| ≤ M₀+d*‖x‖^2) :
    fderiv ℝ (blend (radialCutoff A) F G) x ≠ 0 := by
  have hAp : 0 < A := by linarith
  have hxp : 0 < ‖x‖ := hAp.trans_le hxA
  apply fderiv_ne_zero_of_error_lt h₀
    ((norm_fderiv_blend_sub_le ((contDiff_radialCutoff A).differentiable (by simp) x)
      hF hG (radialCutoff_mem_Icc A x) h₁ hg hv
      (norm_fderiv_radialCutoff_le hAp hunit x)).trans
      (annulus_error_estimate hA hxA hx2A hM₀ hM₁ hB hd))
  exact mul_lt_mul_of_pos_right hscale hxp

end NearbyLagrangian.InfinityRestore

namespace NearbyLagrangian.InfinityRestore

open scoped Topology ContDiff
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

lemma blend_radial_noncritical_outside {F G₀ G : E → ℝ}
    {A c M₀ M₁ B e d : ℝ} (hA : 1 ≤ A)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hunit : ∀ x : E, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ B)
    (hscale : (M₁+B*M₀)/A + e + 2*B*d < c)
    (hF : Differentiable ℝ F) (hG : ∀ x ≠ 0, DifferentiableAt ℝ G x)
    (h₀ : ∀ x, c*‖x‖ ≤ ‖fderiv ℝ G₀ x‖)
    (h₁ : ∀ x, ‖fderiv ℝ F x - fderiv ℝ G₀ x‖ ≤ M₁)
    (hg : ∀ x, ‖fderiv ℝ G x - fderiv ℝ G₀ x‖ ≤ e*‖x‖)
    (hv : ∀ x, |G x - F x| ≤ M₀+d*‖x‖^2)
    {x : E} (hx : A ≤ ‖x‖) : fderiv ℝ (blend (radialCutoff A) F G) x ≠ 0 := by
  have hAp : 0 < A := by linarith
  have hxp : 0 < ‖x‖ := hAp.trans_le hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxp
  by_cases hx2 : ‖x‖ ≤ 2*A
  · exact blend_radial_annulus_noncritical hA hM₀ hM₁ hB hd hunit hscale hx hx2
      (hF x) (hG x hx0) (h₀ x) (h₁ x) (hg x) (hv x)
  · have he : e < c := by
      have hq : 0 ≤ (M₁+B*M₀)/A := div_nonneg (by positivity) hAp.le
      have ht : 0 ≤ 2*B*d := by positivity
      linarith
    rw [(blend_radial_outer_eventuallyEq hAp F G (lt_of_not_ge hx2)).fderiv_eq]
    exact fderiv_ne_zero_of_error_lt (h₀ x) (hg x) (mul_lt_mul_of_pos_right he hxp)

theorem blend_radial_preserves_critical {F G₀ G : E → ℝ}
    {A c M₀ M₁ B e d : ℝ} (hA : 1 ≤ A) (hc : 0 < c)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hunit : ∀ x : E, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ B)
    (hscale : (M₁+B*M₀)/A + e + 2*B*d < c) (hinner : M₁/c < A)
    (hF : Differentiable ℝ F) (hG : ∀ x ≠ 0, DifferentiableAt ℝ G x)
    (h₀ : ∀ x, c*‖x‖ ≤ ‖fderiv ℝ G₀ x‖)
    (h₁ : ∀ x, ‖fderiv ℝ F x - fderiv ℝ G₀ x‖ ≤ M₁)
    (hg : ∀ x, ‖fderiv ℝ G x - fderiv ℝ G₀ x‖ ≤ e*‖x‖)
    (hv : ∀ x, |G x - F x| ≤ M₀+d*‖x‖^2) (x : E) :
    (fderiv ℝ (blend (radialCutoff A) F G) x = 0 ↔ fderiv ℝ F x = 0) ∧
    (fderiv ℝ F x = 0 → blend (radialCutoff A) F G =ᶠ[𝓝 x] F) := by
  have hAp : 0 < A := by linarith
  have hlocal : fderiv ℝ F x = 0 → blend (radialCutoff A) F G =ᶠ[𝓝 x] F := by
    intro hx
    exact blend_radial_inner_eventuallyEq hAp F G
      ((critical_radius_bound hc h₀ h₁ hx).trans_lt hinner)
  refine ⟨⟨?_, fun hx => (hlocal hx).fderiv_eq.trans hx⟩, hlocal⟩
  intro hx
  by_cases hxi : ‖x‖ < A
  · exact (blend_radial_inner_eventuallyEq hAp F G hxi).fderiv_eq.symm.trans hx
  · exact (blend_radial_noncritical_outside hA hM₀ hM₁ hB hd hunit hscale hF hG
      h₀ h₁ hg hv (le_of_not_gt hxi) hx).elim

lemma exists_restoration_radius {c M₀ M₁ B e d : ℝ} 
    (hgap : e + 2*B*d < c) :
    ∃ A : ℝ, 1 ≤ A ∧ M₁/c < A ∧ (M₁+B*M₀)/A + e + 2*B*d < c := by
  let A := max 1 (max (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d))) + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_left (1 : ℝ) (max (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d)))]
  have hAp : 0 < A := by linarith
  have hi : M₁/c < A := by
    dsimp [A]
    linarith [le_max_right (1 : ℝ) (max (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d))),
      le_max_left (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d))]
  have hδ : 0 < c-e-2*B*d := by linarith
  have hlt : (M₁+B*M₀)/(c-e-2*B*d) < A := by
    dsimp [A]
    linarith [le_max_right (1 : ℝ) (max (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d))),
      le_max_right (M₁/c) ((M₁+B*M₀)/(c-e-2*B*d))]
  have hnum : M₁+B*M₀ < A*(c-e-2*B*d) := (div_lt_iff₀ hδ).mp hlt
  have hquot : (M₁+B*M₀)/A < c-e-2*B*d :=
    (div_lt_iff₀ hAp).mpr (by nlinarith)
  exact ⟨A, hA, hi, by linarith⟩

end NearbyLagrangian.InfinityRestore

end

end OAI
