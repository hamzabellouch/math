import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness

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

 omit [CompactSpace M] in
 theorem cost_triangle_split (x m y : M) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    cost x y / (s+t) ≤ cost x m / s + cost m y / t := by
  have htri := dist_triangle x m y
  have hsqr : dist x y ^ 2 ≤ (dist x m+dist m y)^2 :=
    pow_le_pow_left₀ dist_nonneg htri 2
  have hsq := DiscreteVariational.weighted_two_sq (dist x m) (dist m y) s t hs ht
  dsimp only [cost]
  have he₁ : dist x y^2/2/(s+t) = (dist x y^2/(s+t))/2 := by ring
  have he₂ : dist x m^2/2/s+dist m y^2/2/t = (dist x m^2/s+dist m y^2/t)/2 := by ring
  rw [he₁,he₂]
  exact div_le_div_of_nonneg_right
    ((div_le_div_of_nonneg_right hsqr (add_pos hs ht).le).trans hsq) (by norm_num)

 theorem minimizing_shortened_dist {x : M} {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    dist (exp x (s•a)) (exp x (t•a)) = (t-s)*‖a‖ := by
  let p : TangentBundle (model n) M := ⟨x,a⟩
  have hray : dist p.1 (geodesic p 1) = 1*‖p.2‖ := by
    change dist x (geodesic (⟨x,a⟩ : TangentBundle (model n) M) 1) = 1*‖a‖
    rw [← exp_eq_geodesic,one_mul]
    exact ha
  rw [exp_mul_eq_geodesic p s,exp_mul_eq_geodesic p t]
  exact minimizing_segment_dist p hray hs hst ht

 theorem minimizing_shortened_cost {x : M} {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s : ℝ} (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    cost x (exp x (s•a)) = s^2*‖a‖^2/2 := by
  have hd := minimizing_shortened_dist ha (s := 0) (t := s) (le_refl 0) hs hs₁
  simp only [zero_smul,exp_zero,sub_zero] at hd
  dsimp only [cost]
  rw [hd,mul_pow]

 theorem minimizing_tail_injectivity {x : M} {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t < 1) :
    let p : TangentBundle (model n) M := ⟨x,a⟩
    let q := geodesicFlow s p
    (t-s)•q.2 ∈ injectivityDomain q.1 ∧
      exp q.1 ((t-s)•q.2) = exp x (t•a) := by
  let p : TangentBundle (model n) M := ⟨x,a⟩
  let q := geodesicFlow s p
  have hs₁ : s < 1 := hst.trans ht
  have htail : (1-s)•q.2 ∈ minimizingDomain q.1 := by
    change dist q.1 (exp q.1 ((1-s)•q.2)) = ‖(1-s)•q.2‖
    rw [exp_mul_eq_geodesic q (1-s)]
    dsimp only [q]
    rw [geodesic_shift]
    simp only [sub_add_cancel]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs₁),geodesicFlow_norm]
    change dist (geodesic p s) (geodesic p 1) = _
    have hray : dist p.1 (geodesic p 1) = 1*‖p.2‖ := by
      change dist x (geodesic (⟨x,a⟩ : TangentBundle (model n) M) 1) = 1*‖a‖
      rw [← exp_eq_geodesic,one_mul]
      exact ha
    exact minimizing_segment_dist p hray hs hs₁.le le_rfl
  have hr₀ : 0 ≤ (t-s)/(1-s) := div_nonneg (sub_pos.mpr hst).le (sub_pos.mpr hs₁).le
  have hr₁ : (t-s)/(1-s) < 1 := (div_lt_one (sub_pos.mpr hs₁)).mpr (by linarith)
  have hI := strict_radial_mem_injectivity htail hr₀ hr₁
  rw [smul_smul,div_mul_cancel₀ _ (sub_pos.mpr hs₁).ne'] at hI
  refine ⟨hI,?_⟩
  rw [exp_mul_eq_geodesic q (t-s),exp_mul_eq_geodesic p t]
  dsimp only [q]
  rw [geodesic_shift]
  simp only [sub_add_cancel]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
