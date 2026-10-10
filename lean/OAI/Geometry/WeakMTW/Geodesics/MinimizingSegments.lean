import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicDistance

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_segment_dist (p : TangentBundle (model n) M) {L a b : ℝ}
    (hL : dist p.1 (geodesic p L) = L * ‖p.2‖)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    dist (geodesic p a) (geodesic p b) = (b-a) * ‖p.2‖ := by
  have h₁ := geodesic_dist_le p 0 a
  have h₂ := geodesic_dist_le p a b
  have h₃ := geodesic_dist_le p b L
  rw [geodesic_zero,sub_zero,abs_of_nonneg ha] at h₁
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h₂
  rw [abs_of_nonneg (sub_nonneg.mpr hb)] at h₃
  have ht := dist_triangle4 p.1 (geodesic p a) (geodesic p b) (geodesic p L)
  rw [hL] at ht
  nlinarith

 theorem injectivity_extended_minimizer {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : ∃ L : ℝ, 1 < L ∧
      dist x (geodesic (⟨x,v⟩ : TangentBundle (model n) M) L) = L * ‖v‖ := by
  obtain ⟨L,hL,he⟩ := hv
  exact ⟨L,hL,(exp_mul_eq_geodesic (⟨x,v⟩ : TangentBundle (model n) M) L) ▸ he⟩

end
end WeakMTW

namespace DiscreteVariational
 theorem weighted_two_sq (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (x+y)^2/(a+b) ≤ x^2/a + y^2/b := by
  have hsq := sq_nonneg (b*x-a*y)
  apply (div_le_iff₀ (add_pos ha hb)).mpr
  have he : (x^2/a+y^2/b)*(a+b) =
      ((x+y)^2*(a*b)+(b*x-a*y)^2)/(a*b) := by
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ (mul_pos ha hb)).mpr (le_add_of_nonneg_right hsq)

 theorem weighted_three_sq (x y z a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (x+y+z)^2/(a+b+c) ≤ x^2/a + y^2/b + z^2/c := by
  calc
    _ ≤ (x+y)^2/(a+b) + z^2/c := weighted_two_sq (x+y) z (a+b) c (add_pos ha hb) hc
    _ ≤ _ := by linarith [weighted_two_sq x y a b ha hb]
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
