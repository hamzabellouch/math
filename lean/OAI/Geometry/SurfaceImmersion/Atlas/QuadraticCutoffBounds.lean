import OAI.Geometry.SurfaceImmersion.Atlas.QuadraticJetCutoff

namespace OAI

/-! Uniform scale bounds for the local quadratic corrections.  The fixed
cutoff operator makes the constants independent of the tensor and radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

local instance linearNormed : NormedAddCommGroup (Plane →L[ℝ] Space) := inferInstance
local instance linearSpace : NormedSpace ℝ (Plane →L[ℝ] Space) := inferInstance
abbrev SecondTensor := Plane →L[ℝ] Plane →L[ℝ] Space
local instance evalNormed : NormedAddCommGroup ((Plane →L[ℝ] Space) →L[ℝ] Space) := inferInstance
local instance evalSpace : NormedSpace ℝ ((Plane →L[ℝ] Space) →L[ℝ] Space) := inferInstance
local instance evTensorNormed : NormedAddCommGroup (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) := inferInstance
local instance evTensorSpace : NormedSpace ℝ (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) := inferInstance
local instance tensorNormed : NormedAddCommGroup SecondTensor := inferInstance
local instance tensorSpace : NormedSpace ℝ SecondTensor := inferInstance
local instance operatorNormed : NormedAddCommGroup (SecondTensor →L[ℝ] Space) := inferInstance
local instance operatorSpace : NormedSpace ℝ (SecondTensor →L[ℝ] Space) := inferInstance

def unitJetCutoff : ContDiffBump (0 : Plane) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

def quadraticCutoffOperator (x : Plane) : SecondTensor →L[ℝ] Space :=
  ((- (1/2 : ℝ)) * unitJetCutoff x) •
    ((ContinuousLinearMap.apply ℝ Space x).comp
      (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space) x))

lemma quadraticCutoffOperator_apply (x : Plane) (B : SecondTensor) :
    quadraticCutoffOperator x B = cutoffQuadratic B 0 unitJetCutoff x := by
  simp [quadraticCutoffOperator,cutoffQuadratic,quadraticCorrection,smul_smul,mul_comm]

lemma quadraticCutoffOperator_smooth : ContDiff ℝ ∞ quadraticCutoffOperator := by
  let ev₁ : Plane →L[ℝ] ((Plane →L[ℝ] Space) →L[ℝ] Space) := ContinuousLinearMap.apply ℝ Space
  have h₁ : ContDiff ℝ ∞ (fun x : Plane =>
      (ContinuousLinearMap.apply ℝ Space x : (Plane →L[ℝ] Space) →L[ℝ] Space)) := by
    exact ev₁.contDiff
  let ev₂ : Plane →L[ℝ] (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) :=
    ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space)
  have h₂ : ContDiff ℝ ∞ (fun x : Plane =>
      (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space) x : SecondTensor →L[ℝ] (Plane →L[ℝ] Space))) := by
    exact ev₂.contDiff
  exact (contDiff_const.mul unitJetCutoff.contDiff).smul (h₁.clm_comp h₂)

lemma quadraticCutoffOperator_compact : HasCompactSupport quadraticCutoffOperator := by
  apply unitJetCutoff.hasCompactSupport.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp [quadraticCutoffOperator,hx]

theorem uniform_quadratic_cutoff_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ B : SecondTensor, ∀ j ≤ 2, ∀ x : Plane,
      ‖iteratedFDeriv ℝ j (cutoffQuadratic B 0 unitJetCutoff) x‖ ≤ C*‖B‖ := by
  obtain ⟨C,hC,hb⟩ := quadraticCutoffOperator_compact.exists_bound_iteratedFDeriv (𝕜 := ℝ)
    quadraticCutoffOperator_smooth 2
  refine ⟨C,hC,?_⟩
  intro B j hj x
  have he : cutoffQuadratic B 0 unitJetCutoff = fun y => quadraticCutoffOperator y B := by
    funext y
    exact (quadraticCutoffOperator_apply y B).symm
  rw [he]
  calc
    _ ≤ ‖B‖*‖iteratedFDeriv ℝ j quadraticCutoffOperator x‖ :=
      norm_iteratedFDeriv_clm_apply_const quadraticCutoffOperator_smooth.contDiffAt (by simp)
    _ ≤ ‖B‖*C := mul_le_mul_of_nonneg_left (hb j hj x) (norm_nonneg _)
    _ = C*‖B‖ := mul_comm _ _

def scaledQuadraticCutoff (B : SecondTensor) (p : Plane) (r : ℝ) (x : Plane) : Space :=
  r^2 • cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • (x-p))

lemma scaledQuadraticCutoff_smooth (B : SecondTensor) (p : Plane) (r : ℝ) :
    ContDiff ℝ ∞ (scaledQuadraticCutoff B p r) :=
  ((cutoffQuadratic_smooth B 0 unitJetCutoff).comp
    ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul (r^2)

lemma scaledQuadraticCutoff_germ (B : SecondTensor) (p : Plane) {r : ℝ} (hr : 0 < r) :
    scaledQuadraticCutoff B p r =ᶠ[𝓝 p] quadraticCorrection B p := by
  have hc : Continuous (fun x : Plane => r⁻¹ • (x-p)) := by fun_prop
  have ht : Tendsto (fun x : Plane => r⁻¹ • (x-p)) (𝓝 p) (𝓝 0) := by
    simpa only [sub_self,smul_zero] using hc.continuousAt.tendsto (x := p)
  have he := (cutoffQuadratic_germ B 0 unitJetCutoff).comp_tendsto ht
  filter_upwards [he] with x hx
  simp only [Function.comp_apply] at hx
  unfold scaledQuadraticCutoff
  rw [hx]
  simp only [quadraticCorrection,sub_zero,map_smul,smul_apply,smul_smul]
  congr 1
  field_simp [hr.ne']

lemma scaledQuadraticCutoff_tsupport (B : SecondTensor) (p : Plane) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledQuadraticCutoff B p r) ⊆ closedBall p r := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hball
  have hn : r ≤ ‖x-p‖ := (not_le.mp (by simpa only [mem_closedBall_iff_norm] using hball)).le
  have hd : 1 ≤ dist (r⁻¹ • (x-p)) 0 := by
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    simpa only [div_eq_inv_mul] using (one_le_div hr).mpr hn
  have hz := unitJetCutoff.zero_of_le_dist hd
  simp [scaledQuadraticCutoff,cutoffQuadratic,hz] at hx

lemma scaledQuadraticCutoff_norm_deriv (B : SecondTensor) (p : Plane) {r : ℝ}
    (hr : 0 < r) (j : ℕ) (x : Plane) :
    r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ =
      r^2 * ‖iteratedFDeriv ℝ j (cutoffQuadratic B 0 unitJetCutoff)
        (r⁻¹ • (x-p))‖ := by
  have hs := cutoffQuadratic_smooth B 0 unitJetCutoff
  have hc : ContDiff ℝ ∞ (fun x : Plane =>
      cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • (x-p))) :=
    hs.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  unfold scaledQuadraticCutoff
  rw [iteratedFDeriv_const_smul_apply' (hc.of_le (by simp)).contDiffAt]
  rw [iteratedFDeriv_comp_sub (f := fun y => cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • y)) j p x]
  rw [congrFun (iteratedFDeriv_comp_const_smul r⁻¹ (hs.of_le (by simp))) (x-p)]
  rw [norm_smul,norm_smul]
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r),abs_pow,abs_inv,abs_of_pos hr,
    inv_pow]
  field_simp [hr.ne']

/-- The three orders have sizes O(r²), O(r), O(1), with one constant for
all tensors and all positive radii. -/
theorem uniform_scaled_quadratic_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (B : SecondTensor) (p : Plane) (r : ℝ), 0 < r → ∀ j ≤ 2, ∀ x : Plane,
      r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ ≤ C*‖B‖*r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_quadratic_cutoff_bound
  refine ⟨C,hC,?_⟩
  intro B p r hr j hj x
  rw [scaledQuadraticCutoff_norm_deriv B p hr]
  nlinarith [hb B j hj (r⁻¹ • (x-p))]

end ClosedSurfaceR4.SphericalJets

end

end OAI
