import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.DistanceSplitting
import OAI.Geometry.WeakMTW.Coordinates.UnitNormal
import OAI.Geometry.WeakMTW.Geodesics.MinimizingCorner

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_ray_extend {p : TangentBundle (model n) M} (hp : ‖p.2‖ = 1)
    {y : M} {R : ℝ} (hR : 0 < R) (hRd : R < dist p.1 y)
    (hRy : dist (geodesic p R) y = dist p.1 y - R) :
    ∃ T : ℝ, R < T ∧ T ≤ dist p.1 y ∧ dist (geodesic p T) y = dist p.1 y - T := by
  let x := geodesic p R
  obtain ⟨ε,hε,hunit⟩ := locally_exists_unit_ray (n := n) x
  let δ := min ε (dist p.1 y-R) / 2
  have hδ : 0 < δ := div_pos (lt_min hε (sub_pos.mpr hRd)) (by norm_num)
  have hδε : δ < ε := by dsimp only [δ]; linarith [min_le_left ε (dist p.1 y-R)]
  have hδd : δ < dist p.1 y-R := by dsimp only [δ]; linarith [min_le_right ε (dist p.1 y-R)]
  obtain ⟨z,hxz,hzy⟩ := exists_distance_split (n := n) x y (r := δ)
    ⟨hδ.le, by change δ ≤ dist (geodesic p R) y; rw [hRy]; exact hδd.le⟩
  obtain ⟨q,hqx,hq,hqz⟩ := hunit z (by rwa [hxz]) (by rwa [hxz])
  rw [hxz] at hqz
  have hpx : dist p.1 x ≤ R := by
    have hh := geodesic_dist_le p 0 R
    simpa only [geodesic_zero,hp,one_mul,sub_zero,abs_of_pos hR] using hh
  have hpz : dist p.1 z = R+δ := by
    have h1 := dist_triangle p.1 x z
    have h2 := dist_triangle p.1 z y
    rw [hxz] at h1
    change dist z y = dist (geodesic p R) y - δ at hzy
    rw [hRy] at hzy
    rw [hzy] at h2
    linarith
  have hstate : geodesicFlow R p = q :=
    minimizing_broken_eq hp hq hR hδ hqx.symm (by simpa only [hqz, one_mul] using hpz)
  have hnew : geodesic p (R+δ) = z := by
    rw [← hstate,geodesic_shift] at hqz
    simpa only [add_comm δ R] using hqz
  refine ⟨R+δ,by linarith,by linarith,?_⟩
  rw [hnew,hzy]
  change dist (geodesic p R) y - δ = _
  rw [hRy]
  ring

 theorem exists_minimizing_unit_geodesic {x y : M} (hxy : x ≠ y) :
    ∃ p : TangentBundle (model n) M, p.1 = x ∧ ‖p.2‖ = 1 ∧ geodesic p (dist x y) = y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨ε,hε,hunit⟩ := locally_exists_unit_ray (n := n) x
  let r := min ε (dist x y) / 2
  have hr : 0 < r := div_pos (lt_min hε hd) (by norm_num)
  have hrε : r < ε := by dsimp only [r]; linarith [min_le_left ε (dist x y)]
  have hrd : r < dist x y := by dsimp only [r]; linarith [min_le_right ε (dist x y)]
  obtain ⟨z,hxz,hzy⟩ := exists_distance_split (n := n) x y ⟨hr.le,hrd.le⟩
  obtain ⟨p,hpx,hp,hpz⟩ := hunit z (by rwa [hxz]) (by rwa [hxz])
  rw [hxz] at hpz
  let S : Set ℝ := Icc r (dist x y) ∩ {t | dist (geodesic p t) y = dist x y-t}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_eq ((geodesic_smooth p).continuous.dist continuous_const) (continuous_const.sub continuous_id))
  have hrS : r ∈ S := ⟨⟨le_rfl,hrd.le⟩,by simpa only [mem_ofPred_eq,hpz] using hzy⟩
  obtain ⟨R,hRS,hmax⟩ := hS.exists_isGreatest ⟨r,hrS⟩
  have hR : R = dist x y := by
    by_contra hne
    have hRlt : R < dist x y := lt_of_le_of_ne hRS.1.2 hne
    obtain ⟨T,hRT,hTd,hTy⟩ := minimizing_ray_extend hp (y := y)
      (hr.trans_le hRS.1.1) (by rwa [hpx]) (by simpa only [mem_ofPred_eq,hpx] using hRS.2)
    have hTS : T ∈ S := ⟨⟨hRS.1.1.trans hRT.le,by simpa only [hpx] using hTd⟩,
      by simpa only [mem_ofPred_eq,hpx] using hTy⟩
    exact (not_lt_of_ge (hmax hTS)) hRT
  refine ⟨p,hpx,hp,?_⟩
  apply dist_eq_zero.mp
  have hh : dist (geodesic p R) y = dist x y-R := hRS.2
  rwa [hR,sub_self] at hh

 theorem exists_minimizing_vector (x y : M) :
    ∃ v : TangentSpace (model n) x, exp x v = y ∧ ‖v‖ = dist x y := by
  by_cases he : x = y
  · subst y
    exact ⟨0,exp_zero x,by simp⟩
  obtain ⟨⟨z,w⟩,hpx,hp,he⟩ := exists_minimizing_unit_geodesic (n := n) he
  dsimp only at hpx hp he
  subst z
  refine ⟨dist x y • w,?_,?_⟩
  · exact (exp_mul_eq_geodesic (⟨x,w⟩ : TangentBundle (model n) M) (dist x y)).trans he
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg dist_nonneg,hp,mul_one]
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
