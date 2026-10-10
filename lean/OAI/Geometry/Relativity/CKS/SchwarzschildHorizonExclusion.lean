import OAI.Geometry.Relativity.CKS.SurfaceBarrier
import OAI.Geometry.Relativity.CKS.SurfaceParameter

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma local_surface_barrier {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m < ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) (N : E3)
    (hunit : cartMetric m (f y) N N = 1)
    (horth : ∀ a, cartMetric m (f y) N (fderiv ℝ f y a) = 0) :
    |parameterTensorTrace m f y| < |parameterMeanCurvature m f y N| := by
  have hd := hf.differentiableAt (by simp)
  have hh := outward_surface_mean_bound hm hf hmax hr.le hinj
  have ht := tangent_surface_tensor_trace hm hd hmax hr.le hinj
  have hp : 0 < ‖f y‖ := lt_trans (by positivity) hr
  have hu := lapse_dominates_velocity hm hr
  have hs : |parameterTensorTrace m f y| < parameterMeanCurvature m f y (radialNormal m (f y)) := by
    apply lt_of_lt_of_le _ hh
    rw [ht,abs_div,abs_mul,abs_of_pos hp]
    norm_num
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hu (by norm_num)) hp
  rcases normal_radial_at_tangent hm hr.le _ hinj (maximum_radius_tangent hd hmax) N hunit horth with hN | hN
  · rw [hN]
    exact lt_of_lt_of_le hs (le_abs_self _)
  · rw [hN,parameterMeanCurvature_neg,abs_neg]
    exact lt_of_lt_of_le hs (le_abs_self _)

universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

theorem closed_surface_barrier {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : InteriorImmersion m T) :
    ∃ p, |surfaceTensorTrace m D.map p| < |surfaceMeanCurvature m D.map D.normal p| := by
  have hc : Continuous (fun p => ‖D.map p‖^2) := D.smooth.continuous.norm.pow 2
  obtain ⟨p,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  refine ⟨p,?_⟩
  unfold surfaceTensorTrace surfaceMeanCurvature
  apply local_surface_barrier hm (surfaceParameter_smooth D.smooth p)
    (surfaceParameter_maximum (fun q => hmax (Set.mem_univ q)))
  · simpa only [surfaceParameter_center] using D.interior p
  · rw [surfaceParameter_derivative D.smooth p]
    exact D.immersion p
  · simpa only [surfaceParameter_center] using D.normal_unit p
  · intro a
    rw [surfaceParameter_center,surfaceParameter_derivative D.smooth p]
    exact D.normal_orthogonal p a

theorem no_closed_apparent_horizon {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : InteriorImmersion m T) :
    ¬ (∀ p, surfaceMeanCurvature m D.map D.normal p + surfaceTensorTrace m D.map p = 0 ∨
      surfaceMeanCurvature m D.map D.normal p - surfaceTensorTrace m D.map p = 0) := by
  obtain ⟨p,hp⟩ := closed_surface_barrier hm D
  intro hh
  rcases hh p with hp' | hp'
  · have he : surfaceMeanCurvature m D.map D.normal p = -surfaceTensorTrace m D.map p := by linarith
    rw [he,abs_neg] at hp
    exact (lt_irrefl _ hp)
  · have he : surfaceMeanCurvature m D.map D.normal p = surfaceTensorTrace m D.map p := by linarith
    rw [he] at hp
    exact (lt_irrefl _ hp)

end CKSSchwarzschild

end

end OAI
