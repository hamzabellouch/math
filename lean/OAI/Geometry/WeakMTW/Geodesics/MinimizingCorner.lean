import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicDistance
import OAI.Geometry.WeakMTW.Geodesics.NoCorner

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

 theorem geodesic_no_corner {p q : TangentBundle (model n) M}
    {C : ℝ} (hp : ‖p.2‖ = C) (hq : ‖q.2‖ = C) (h0 : p.1 = q.1)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (geodesic p (-t)) (geodesic q t) = 2*C*t) : p = q := by
  have hh := intrinsic_no_corner (geodesic_smooth p) (geodesic_smooth q)
    (hp ▸ norm_nonneg p.2) (hp ▸ geodesic_dist p 0) (hq ▸ geodesic_dist q 0)
    (by simpa only [geodesic_zero] using h0) he
  simpa only [geodesic_state_zero] using hh

 theorem minimizing_broken_eq {p q : TangentBundle (model n) M}
    {C : ℝ} (hp : ‖p.2‖ = C) (hq : ‖q.2‖ = C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hjoin : geodesic p a = q.1)
    (hd : dist p.1 (geodesic q b) = C * (a+b)) : geodesicFlow a p = q := by
  apply geodesic_no_corner (by rw [geodesicFlow_norm,hp]) hq hjoin
  have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hta : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a :=
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  have htb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [htpos,hta,htb] with t ht hta htb
  rw [geodesic_shift]
  change dist (geodesic p (-t+a)) (geodesic q t) = 2*C*t
  have h1 := geodesic_dist_le p 0 (-t+a)
  have h2 := geodesic_dist_le p (-t+a) a
  have h3 := geodesic_dist_le q 0 t
  have h4 := geodesic_dist_le q t b
  rw [hp,geodesic_zero,sub_zero,abs_of_nonneg (by linarith)] at h1
  rw [hp,show a-(-t+a)=t by ring,abs_of_pos ht,hjoin] at h2
  rw [hq,geodesic_zero,sub_zero,abs_of_pos ht] at h3
  rw [hq,abs_of_pos (sub_pos.mpr htb)] at h4
  have hlo := dist_triangle p.1 (geodesic p (-t+a)) (geodesic q b)
  have hlo' := dist_triangle (geodesic p (-t+a)) (geodesic q t) (geodesic q b)
  rw [hd] at hlo
  have hhi := dist_triangle (geodesic p (-t+a)) q.1 (geodesic q t)
  linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
