import OAI.Analysis.NumericalRange.Sharpness

namespace OAI

universe u_244

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
def G : ℂ → ℂ := exteriorMap D.exterior.leading D.exterior.constant D.exterior.regular
def ψ : ℂ → ℂ := D.interior.toDisk ∘ D.G
lemma circle_collar {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.exterior.radius⁻¹ < ‖t‖ := by
  rw [mem_sphere_zero_iff_norm.mp ht]
  exact inv_lt_one_of_one_lt₀ D.exterior.radius_gt
lemma G_analytic : AnalyticOnNhd ℂ D.G (sphere 0 1) :=
  (exteriorCoordinate_analytic D.exterior).mono (fun _ ht => D.circle_collar ht)
lemma G_boundary {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.G t ∈ frontier D.domain :=
  D.exterior.boundary_image ▸ mem_image_of_mem D.G ht
lemma toDisk_maps : MapsTo D.interior.toDisk D.domain (ball 0 1) := by
  intro z hz
  exact D.interior.image_domain ▸ mem_image_of_mem D.interior.toDisk hz
lemma disk_boundary {z : ℂ} (hz : z ∈ frontier D.domain) :
    D.interior.toDisk z ∈ sphere (0:ℂ) 1 := by
  obtain ⟨w,hw,he⟩ := D.interior.inverse_sphere_frontier D.isOpen ▸ hz
  rw [← he,D.interior.right_inverse w (D.interior.closedDisk_subset (sphere_subset_closedBall hw))]
  exact hw
lemma ψ_analytic : AnalyticOnNhd ℂ D.ψ (sphere 0 1) := by
  intro t ht
  exact (D.interior.analytic_to _ (D.interior.closure_subset (D.G_boundary ht).1)).comp
    (D.G_analytic t ht)
lemma ψ_boundary {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : ‖D.ψ t‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (D.disk_boundary (D.G_boundary ht))
lemma inverse_ψ {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.interior.fromDisk (D.ψ t) = D.G t :=
  D.interior.left_inverse _ (D.interior.closure_subset (D.G_boundary ht).1)
lemma ψ_jacobian {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) :
    0 ≤ t*deriv D.ψ t/D.ψ t := by
  rw [Complex.nonneg_iff]
  refine ⟨circle_log_derivative_nonneg (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (D.ψ_boundary ht) ?_,
    (circle_log_derivative_real (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (fun z hz => D.ψ_boundary (mem_sphere_zero_iff_norm.mpr hz))).symm⟩
  have hi : D.exterior.radius⁻¹ < 1 := inv_lt_one_of_one_lt₀ D.exterior.radius_gt
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hi)] with r hr hri
  have hr0 : 0 < r := (inv_pos.mpr (zero_lt_one.trans D.exterior.radius_gt)).trans hri
  have hnorm : ‖(r:ℂ)*t‖ = r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,mem_sphere_zero_iff_norm.mp ht,mul_one]
  change ‖D.interior.toDisk (D.G ((r:ℂ)*t))‖ ≤ 1
  apply mem_closedBall_zero_iff.mp (D.interior.closure_maps _)
  rcases lt_or_eq_of_le (show r ≤ 1 from hr) with hlt|rfl
  · exact subset_closure ((D.exterior.interior_iff _ (by simpa only [hnorm] using hri)).mpr
      (mem_ball_zero_iff.mpr (by simpa only [hnorm] using hlt)))
  · simpa only [ofReal_one,one_mul] using (D.G_boundary ht).1
lemma G_ne_interior {z : ℂ} (hz : z ∈ D.domain) {t : ℂ} (ht : 1 ≤ ‖t‖) : D.G t ≠ z := by
  intro he
  rcases lt_or_eq_of_le ht with hlt|heq
  · apply D.exterior.outside t hlt
    change D.G t ∈ closure D.domain
    rw [he]
    exact subset_closure hz
  · have hb := D.G_boundary (mem_sphere_zero_iff_norm.mpr heq.symm)
    rw [D.isOpen.frontier_eq] at hb
    exact hb.2 (he.symm ▸ hz)
lemma G_mass {z : ℂ} (hz : z ∈ D.domain) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ) /
      (D.G (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  apply exterior_cauchy_kernel_integral D.exterior.leading_ne
    (D.exterior.analytic_regular.mono (closedBall_subset_ball D.exterior.radius_gt))
  intro t ht
  exact D.G_ne_interior hz ht
lemma ψ_mass {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.ψ (t.toCircle : ℂ) /
      (D.ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  have ha := D.interior.inverse_ball z hz
  have hfa := D.interior.right_inverse z (D.interior.closedDisk_subset (ball_subset_closedBall hz))
  have hm := conformal_circle_mass D.convex.closure D.interior.outer_open
    D.interior.closure_subset D.interior.analytic_to D.interior.injective_to D.G_analytic
    (fun t ht => (D.G_boundary ht).1) (subset_closure ha)
    (D.interior.noncritical_to _ (D.interior.closure_subset (subset_closure ha)))
    (fun t ht => D.G_ne_interior ha (mem_sphere_zero_iff_norm.mp ht).ge) (D.G_mass ha)
  simpa only [hfa,ψ,Function.comp_apply] using hm
lemma support_circle (w t : Circle) :
    0 ≤ (conj ((t:ℂ)*deriv D.G t)*(D.G t-D.G w)).re :=
  D.support t t.2 _ (D.G_boundary w.2).1
end AdmissibleDomain

variable {n : Type u_244} [Fintype n] [DecidableEq n]
lemma spectrum_matrixAnalyticEval_subset (A : Matrix n n ℂ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z) :
    spectrum ℂ (matrixAnalyticEval A f) ⊆ f '' spectrum ℂ A := by
  intro w hw
  by_contra hn
  have hne (z : ℂ) (hz : z ∈ spectrum ℂ A) : w-f z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hn ⟨z,hz,h.symm⟩)
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun v => w-f v) z :=
    analyticAt_const.sub (hf z hz)
  have hh (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun v => (w-f v)⁻¹) z :=
    (hg z hz).inv (hne z hz)
  have he : matrixAnalyticEval A (fun v => (w-f v)*(w-f v)⁻¹) = 1 := by
    rw [matrixAnalyticEval_eventuallyEq A (g := fun _ => 1)]
    · simp [matrixAnalyticEval_const]
    · intro z hz
      filter_upwards [(hg z hz).continuousAt.eventually_ne (hne z hz)] with v hv
      exact mul_inv_cancel₀ hv
  rw [matrixAnalyticEval_mul A hg hh,matrixAnalyticEval_sub A (fun _ _ => analyticAt_const) hf,
    matrixAnalyticEval_const] at he
  have hu : IsUnit (algebraMap ℂ (Matrix n n ℂ) w-matrixAnalyticEval A f) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at hh
    exact zero_ne_one hh
  exact (spectrum.notMem_iff.mpr hu) hw

lemma matrixAnalyticEval_stable [Nonempty n] (A : Matrix n n ℂ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hb : ∀ z ∈ spectrum ℂ A, ‖f z‖ < 1) :
    spectralRadius ℂ (matrixAnalyticEval A f) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt (matrixAnalyticEval A f) (r := 1)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := spectrum_matrixAnalyticEval_subset A hf hz
  exact_mod_cast hb w hw
end CompleteCrouzeix

end

end

end OAI
