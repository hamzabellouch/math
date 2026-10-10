import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

noncomputable section

namespace Invariant233

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inverse_graph_mem_iff {H : E →ₗ.[ℂ] E}
    (hinj : Function.Injective H) {x y : E} :
    (x, y) ∈ H.inverse.graph ↔ (y, x) ∈ H.graph := by
  rw [LinearPMap.inverse_graph (LinearPMap.ker_eq_bot.mpr hinj)]
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap,
    LinearEquiv.symm_prodComm, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply,
    Prod.swap_prod_mk]

theorem injective_inverse {H : E →ₗ.[ℂ] E} (hinj : Function.Injective H) :
    Function.Injective H.inverse := by
  intro y z hyz
  apply Subtype.ext
  exact H.mem_graph_snd_inj
    ((inverse_graph_mem_iff hinj).mp (H.inverse.mem_graph y))
    ((inverse_graph_mem_iff hinj).mp (H.inverse.mem_graph z)) hyz

theorem inverse_inverse {H : E →ₗ.[ℂ] E} (hinj : Function.Injective H) :
    H.inverse.inverse = H := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rcases z with ⟨x, y⟩
  rw [inverse_graph_mem_iff (injective_inverse hinj), inverse_graph_mem_iff hinj]

variable [CompleteSpace E]

theorem dense_range_of_selfAdjoint_injective {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) (hinj : Function.Injective H) :
    Dense (H.toFun.range : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  have hinner : ∀ x : H.domain, inner ℂ y (H x) = 0 := by
    intro x
    exact (H.toFun.range.mem_orthogonal' y).mp hy (H x) ⟨x, rfl⟩
  have hyD : y ∈ H.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨0, by
      intro x
      simp only [inner_zero_left, hinner x]⟩
  have hyA : H.adjoint ⟨y, hyD⟩ = 0 :=
    LinearPMap.adjoint_apply_eq hH.dense_domain _ (by
      intro x
      simp only [inner_zero_left, hinner x])
  have hyG : (y, 0) ∈ H.graph := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hH]
    exact H.adjoint.mem_graph_iff.mpr ⟨⟨y, hyD⟩, rfl, hyA⟩
  obtain ⟨x, hxy, hx0⟩ := H.mem_graph_iff.mp hyG
  have hx : x = 0 := hinj (hx0.trans H.toFun.map_zero.symm)
  exact hxy.symm.trans (congrArg Subtype.val hx)

theorem dense_domain_inverse_of_selfAdjoint_injective {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) (hinj : Function.Injective H) :
    Dense (H.inverse.domain : Set E) := by
  rw [LinearPMap.inverse_domain]
  exact dense_range_of_selfAdjoint_injective hH hinj

theorem selfAdjoint_inverse_of_injective {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) (hinj : Function.Injective H) :
    IsSelfAdjoint H.inverse := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (dense_domain_inverse_of_selfAdjoint_injective hH hinj)]
  ext z
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hz
    have hswap : (z.2, z.1) ∈ H.adjoint.graph := by
      rw [LinearPMap.adjoint_graph_eq_graph_adjoint hH.dense_domain,
        Submodule.mem_adjoint_iff]
      intro a b hab
      have h := hz b a ((inverse_graph_mem_iff hinj).mpr hab)
      exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
    rw [LinearPMap.isSelfAdjoint_def.mp hH] at hswap
    exact (inverse_graph_mem_iff hinj).mpr hswap
  · intro hz a b hab
    have hswap := (inverse_graph_mem_iff hinj).mp hz
    rw [← LinearPMap.isSelfAdjoint_def.mp hH,
      LinearPMap.adjoint_graph_eq_graph_adjoint hH.dense_domain,
      Submodule.mem_adjoint_iff] at hswap
    have h := hswap b a ((inverse_graph_mem_iff hinj).mp hab)
    exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

omit [CompleteSpace E] in
theorem IsPositivePartial.inverse {H : E →ₗ.[ℂ] E}
    (hpos : IsPositivePartial H) (hinj : Function.Injective H) :
    IsPositivePartial H.inverse := by
  intro y
  have hy : (y : E) ∈ H.toFun.range := by
    simpa only [LinearPMap.inverse_domain] using y.property
  obtain ⟨x, hx⟩ := hy
  have hxy : H x = (y : E) := hx
  rw [LinearPMap.inverse_apply_eq (LinearPMap.ker_eq_bot.mpr hinj) hxy, ← hxy]
  change 0 ≤ RCLike.re (inner ℂ (H x) (x : E))
  rw [inner_re_symm]
  exact hpos x

end Invariant233

end

end OAI
