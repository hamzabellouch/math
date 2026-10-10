import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodFacetSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem facet_forcing_tube (B : Body E) (x y n c : E) (a r R ε : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier) (hn : ‖n‖=1)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y) ≤ 0)
    (ha : 0<a) (hr : 0<r) (hε : 0<ε)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    ∃δ : ℝ,0<δ ∧ ∀v : ℝ → E,ContinuousOn v (Icc 0 1) →
      (∀t∈Icc (0:ℝ) 1,‖v t-facetDriver x y n a t‖ < δ) →
      ∃u k : ℝ → E,ContinuousOn u (Icc 0 1) ∧ ContinuousOn k (Icc 0 1) ∧
        u 0=x ∧ k 0=0 ∧
        (∀t∈Icc (0:ℝ) 1,u t∈B.carrier ∧ u t=x+(v t-v 0)+k t) ∧
        TendstoUniformlyOn (fun m => mesh B x v (m+1)) u atTop (Icc 0 1) ∧
        BoundedVariationOn k (Icc (0:ℝ) 1) ∧ NormalPartitionCondition B u k ∧
        (∀t∈Icc (0:ℝ) 1,‖u t-facetPath x y t‖ < ε) ∧
        a/2 < inner ℝ n (k (1/2)-k 1) := by
  have hw : ContinuousOn (facetDriver x y n a) (Icc 0 1) :=
    (facetDriver_continuous x y n a).continuousOn
  obtain ⟨u₀,hu₀,hBu₀,hconv₀,hcont⟩ :=
    reflected_driver_continuity B x c r R hx hr hball hR (facetDriver x y n a) hw
  have huEq : ∀t∈Icc (0:ℝ) 1,u₀ t=facetPath x y t := by
    intro t ht
    exact tendsto_nhds_unique (hconv₀.tendsto_at ht) (facet_mesh_tendsto B x y n a hx hy hsupport ha.le t ht.1)
  let η := min ε (a/8)
  have hη : 0<η := lt_min hε (by positivity)
  have hηε : η≤ε := min_le_left _ _
  have hηa : η≤a/8 := min_le_right _ _
  obtain ⟨δ,hδ,hδtube⟩ := hcont η hη
  refine ⟨δ,hδ,fun v hv hc => ?_⟩
  obtain ⟨z,hz,hBz,hconvz,hclose⟩ := hδtube v hv hc
  obtain ⟨u,k,μ,hu,hk,hu₀,hk₀,hBu,hconv,hBV,hNormal,hrest⟩ :=
    reflected_equation B x c r R hx hr hball hR v hv
  have hzEq : ∀t∈Icc (0:ℝ) 1,z t=u t := by
    intro t ht
    exact tendsto_nhds_unique (hconvz.tendsto_at ht) (hconv.tendsto_at ht)
  have huclose : ∀t∈Icc (0:ℝ) 1,‖u t-facetPath x y t‖ < η := by
    intro t ht
    have hb := hclose t ht
    rw [hzEq t ht,huEq t ht] at hb
    exact lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) hb
  have hkclose : ∀t∈Icc (0:ℝ) 1,
      ‖k t-(facetPath x y t-x-(facetDriver x y n a t-facetDriver x y n a 0))‖ < η := by
    intro t ht
    have hb := hclose t ht
    rw [hzEq t ht,huEq t ht] at hb
    have he : u t-x-(v t-v 0)=k t := by rw [(hBu t ht).2];abel
    rw [he] at hb
    exact lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) hb
  refine ⟨u,k,hu,hk,hu₀,hk₀,hBu,hconv,hBV,hNormal,
    fun t ht => (huclose t ht).trans_le hηε,?_⟩
  have hhalf : ‖k (1/2)‖ < η := by
    have hb := hkclose (1/2) ⟨by norm_num,by norm_num⟩
    have he : facetPath x y (1/2)-x-(facetDriver x y n a (1/2)-facetDriver x y n a 0)=0 := by
      norm_num [facetPath,facetDriver]
    simpa only [he,sub_zero] using hb
  have hend : ‖k 1+a • n‖ < η := by
    have hb := hkclose 1 ⟨zero_le_one,le_rfl⟩
    have he : facetPath x y 1-x-(facetDriver x y n a 1-facetDriver x y n a 0)=-(a • n) := by
      norm_num [facetPath,facetDriver]
    simpa only [he,sub_neg_eq_add] using hb
  have hnorm : ‖k (1/2)-(k 1+a • n)‖ < 2*η :=
    (norm_sub_le _ _).trans_lt (by linarith)
  have hi := (abs_le.mp (abs_real_inner_le_norm n (k (1/2)-(k 1+a • n)))).1
  rw [hn,one_mul] at hi
  have he : inner ℝ n (k (1/2)-k 1)=inner ℝ n (k (1/2)-(k 1+a • n))+a := by
    rw [inner_sub_right,inner_sub_right,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn]
    ring
  rw [he]
  linarith

end ConvexSkorokhod

end OAI
