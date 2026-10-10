import Mathlib
import OAI.Probability.LatticeSurface.Convexity.FreeHilbert
import OAI.Probability.LatticeSurface.Dynamics.ProjectionMesh
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodRegularity

namespace OAI

namespace ProjectionComparison

open Set ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def pathIncrement (S : System V E) (w : ℝ → FreeSpace S) (N : ℕ) (i : ℕ) : V → ℝ :=
  extendFree S (fun _ => 0) (w ((i+1:ℕ)/(N:ℝ))-w ((i:ℝ)/N))

noncomputable def pathMesh (S : System V E) (b h : V → ℝ) (hh : h∈feasible S b)
    (w : ℝ → FreeSpace S) (N : ℕ) (t : ℝ) : V → ℝ :=
  recursion S b ⟨h,hh⟩ h (pathIncrement S w N) ⌊t*N⌋₊

def pathTail (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (a t : ℝ) : {x // x∉S.pins} → ℝ :=
  fun x => max (u₁ t x-u₀ t x-a) 0

end ProjectionComparison

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
lemma coordinates_extendFree (S : System V E) (b : V → ℝ) (v : FreeSpace S) :
    freeCoordinates S (extendFree S b v)=v := by
  apply PiLp.ext
  intro x
  simp [freeCoordinates,extendFree,x.property]

omit [Fintype E] in
lemma pathMesh_eq_hilbert (S : System V E) (b h : V → ℝ) (hh : h∈feasible S b)
    (B : ConvexSkorokhod.Body (FreeSpace S))
    (he : ∀v:V → ℝ,extendFree S b (ConvexSkorokhod.project B (freeCoordinates S v))=project S b ⟨h,hh⟩ v)
    (w : ℝ → FreeSpace S) (N : ℕ) (t : ℝ) :
    pathMesh S b h hh w N t=
      extendFree S b (ConvexSkorokhod.mesh B (freeCoordinates S h) w N t) := by
  have hne : (feasible S b).Nonempty := ⟨h,hh⟩
  have hi : ∀i,recursion S b hne h (pathIncrement S w N) i=
      extendFree S b (ConvexSkorokhod.walk B (freeCoordinates S h) (ConvexSkorokhod.sampledDriver w N) i) := by
    intro i
    induction i with
    | zero => exact (extendFree_coordinates S b h hh.2).symm
    | succ i ih =>
      rw [ProjectionComparison.recursion,←he,ConvexSkorokhod.walk,ih]
      apply congrArg (extendFree S b)
      apply congrArg (ConvexSkorokhod.project B)
      apply PiLp.ext
      intro x
      simp [freeCoordinates,extendFree,x.property,pathIncrement,ConvexSkorokhod.sampledDriver]
  exact hi _

omit [Fintype E] in
lemma extendFree_lipschitz (S : System V E) (b : V → ℝ) : LipschitzWith 1 (extendFree S b) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (u-v))).mpr
  intro x
  by_cases hx : x∈S.pins
  · simp only [Pi.sub_apply,extendFree,dite_eq_left hx,sub_self,norm_zero]
    exact norm_nonneg _
  · simpa only [Pi.sub_apply,extendFree,dite_eq_right hx,PiLp.sub_apply] using PiLp.norm_apply_le (u-v) ⟨x,hx⟩

omit [Fintype E] in
lemma exists_projection_path (S : System V E) (b h : V → ℝ) (hh : h∈feasible S b)
    (c : FreeSpace S) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r⊆freeCarrier S b)
    (w : ℝ → FreeSpace S) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2) :
    ∃u : ℝ → V → ℝ,ContinuousOn u (Icc 0 1) ∧ u 0=h ∧
      (∀t∈Icc (0:ℝ) 1,u t∈feasible S b) ∧
      TendstoUniformlyOn (fun n => pathMesh S b h hh w (n+1)) u atTop (Icc 0 1) := by
  obtain ⟨B,hB,he⟩ := exists_free_body S b ⟨h,hh⟩
  have hh' : freeCoordinates S h∈B.carrier := by
    rw [hB];change extendFree S b (freeCoordinates S h)∈feasible S b
    rwa [extendFree_coordinates S b h hh.2]
  obtain ⟨v,hvcont,hv,hvmem,hvvar⟩ := ConvexSkorokhod.projection_mesh_regular_limit B
    (freeCoordinates S h) c r hh' hr (by rwa [hB]) w hw hosc
  let u := fun t => extendFree S b (v t)
  have hlim : TendstoUniformlyOn (fun n => pathMesh S b h hh w (n+1)) u atTop (Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv ε hε] with n hn t ht
    rw [pathMesh_eq_hilbert S b h hh B he]
    exact ((extendFree_lipschitz S b).dist_le_mul _ _).trans_lt (by simpa using hn t ht)
  refine ⟨u,(extendFree_continuous S b).comp_continuousOn hvcont,?_,fun t ht => ?_,hlim⟩
  · have hhlim := hlim.tendsto_at (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
    have hhmesh : (fun n => pathMesh S b h hh w (n+1) 0)=fun _ : ℕ => h := by
      funext n;simp [pathMesh,recursion]
    rw [hhmesh] at hhlim
    exact tendsto_nhds_unique hhlim tendsto_const_nhds
  · have hmem := hvmem t ht
    rwa [hB] at hmem

end ProjectionComparison

end OAI
