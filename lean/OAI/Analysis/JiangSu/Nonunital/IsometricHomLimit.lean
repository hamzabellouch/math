import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace NonunitalIntertwining
open Filter Topology

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

 theorem pointwise_cauchy_of_dense (φ : ℕ → A →⋆ₙₐ[ℂ] B)
    (a : ℕ → A) (ha : DenseRange a) (hc : ∀ j,CauchySeq (fun n => φ n (a j))) :
    ∀ x : A,CauchySeq (fun n => φ n x) := by
  intro x
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := ha.exists_dist_lt x (by positivity : 0<ε/4)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc j) (ε/2) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h1 : dist (φ m x) (φ m (a j))≤dist x (a j) :=
    by simpa only [dist_eq_norm,←map_sub] using NonUnitalStarAlgHom.norm_apply_le (φ m) (x-a j)
  have h2 : dist (φ n (a j)) (φ n x)≤dist (a j) x :=
    by simpa only [dist_eq_norm,←map_sub] using NonUnitalStarAlgHom.norm_apply_le (φ n) (a j-x)
  have h3 := hN m hm n hn
  have hb := dist_triangle4 (φ m x) (φ m (a j)) (φ n (a j)) (φ n x)
  rw [dist_comm (a j) x] at h2
  linarith

 theorem exists_limit_hom (φ : ℕ → A →⋆ₙₐ[ℂ] B)
    (a : ℕ → A) (ha : DenseRange a) (hc : ∀ j,CauchySeq (fun n => φ n (a j))) :
    ∃ ψ : A →⋆ₙₐ[ℂ] B, ∀ x,Tendsto (fun n => φ n x) atTop (𝓝 (ψ x)) := by
  have hh := pointwise_cauchy_of_dense φ a ha hc
  choose f hf using fun x => cauchySeq_tendsto_of_complete (hh x)
  let ψ : A →⋆ₙₐ[ℂ] B := {
    toFun := f
    map_zero' := by
      apply tendsto_nhds_unique (hf 0)
      simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:B)) atTop (𝓝 0))
    map_mul' := by
      intro x y
      apply tendsto_nhds_unique (hf (x*y))
      simpa only [map_mul] using (hf x).mul (hf y)
    map_add' := by
      intro x y
      apply tendsto_nhds_unique (hf (x+y))
      simpa only [map_add] using (hf x).add (hf y)
    map_smul' := by
      intro c x
      apply tendsto_nhds_unique (hf (c • x))
      simpa only [map_smul,MonoidHom.id_apply] using (hf x).const_smul c
    map_star' := by
      intro x
      apply tendsto_nhds_unique (hf (star x))
      simpa only [map_star] using (hf x).star }
  exact ⟨ψ,hf⟩

 theorem limit_hom_isometry (φ : ℕ → A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ n,Isometry (φ n)) (ψ : A →⋆ₙₐ[ℂ] B)
    (hψ : ∀ x,Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) : Isometry ψ := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  apply tendsto_nhds_unique ((hψ x).norm)
  have hn (n : ℕ) : ‖φ n x‖=‖x‖ :=
    (AddMonoidHomClass.isometry_iff_norm (φ n)).mp (hφ n) x
  simpa only [hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))

end NonunitalIntertwining

end
end

end OAI
