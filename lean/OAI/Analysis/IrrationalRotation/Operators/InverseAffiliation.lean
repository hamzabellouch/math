import OAI.Analysis.IrrationalRotation.Operators.NormalAffiliatedTransport

namespace OAI

noncomputable section

namespace Invariant233

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem IsAffiliated.inverse
    {M : VonNeumannAlgebra E} {H : E →ₗ.[ℂ] E} (hH : IsAffiliated M H)
    (hinj : Function.Injective H) : IsAffiliated M H.inverse := by
  have hker : H.toFun.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hpartialker : H.ker = ⊥ := by simp [LinearPMap.ker, hker]
  intro U hU
  have hgraph : ∀ y : H.inverse.domain,
      ((U : E →L[ℂ] E) (y : E), (U : E →L[ℂ] E) (H.inverse y)) ∈
        H.inverse.graph := by
    intro y
    have hy : (y : E) ∈ H.toFun.range := by
      simpa only [LinearPMap.inverse_domain] using y.property
    obtain ⟨x, hx⟩ := hy
    have hxy : H x = (y : E) := hx
    have hyx : H.inverse y = (x : E) := LinearPMap.inverse_apply_eq hpartialker hxy
    obtain ⟨hD, hC⟩ := hH.commutes_of_mem_commutant hU
    rw [hyx, ← hxy, ← hC x]
    exact LinearPMap.mem_inverse_graph hpartialker ⟨(U : E →L[ℂ] E) x, hD x⟩
  let hD : ∀ y : H.inverse.domain, (U : E →L[ℂ] E) (y : E) ∈ H.inverse.domain :=
    fun y => LinearPMap.mem_domain_of_mem_graph (hgraph y)
  refine ⟨hD, fun y => ?_⟩
  exact H.inverse.mem_graph_snd_inj (H.inverse.mem_graph ⟨(U : E →L[ℂ] E) y, hD y⟩)
    (hgraph y) rfl

end Invariant233

end

end OAI
