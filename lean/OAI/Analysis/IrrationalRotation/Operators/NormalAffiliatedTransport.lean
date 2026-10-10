import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransport
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

noncomputable section

namespace Invariant233

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem IsAffiliated.graph_mem_of_mem_commutant
    {M : VonNeumannAlgebra E} {H : E →ₗ.[ℂ] E} (hH : IsAffiliated M H)
    {W : E →L[ℂ] E} (hW : W ∈ M.commutant) (x : H.domain) :
    (W (x : E), W (H x)) ∈ H.graph := by
  let S : Submodule ℂ M.commutant := {
    carrier := {a | ∀ z : H.domain,
      ((a : E →L[ℂ] E) (z : E), (a : E →L[ℂ] E) (H z)) ∈ H.graph}
    zero_mem' := by
      intro z
      simp
    add_mem' := by
      intro a b ha hb z
      change ((a : E →L[ℂ] E) z + (b : E →L[ℂ] E) z,
        (a : E →L[ℂ] E) (H z) + (b : E →L[ℂ] E) (H z)) ∈ H.graph
      exact H.graph.add_mem (ha z) (hb z)
    smul_mem' := by
      intro c a ha z
      simpa only [SetLike.val_smul, smul_apply, Prod.smul_mk]
        using H.graph.smul_mem c (ha z) }
  have hspan : Submodule.span ℂ (unitary M.commutant : Set M.commutant) ≤ S := by
    apply Submodule.span_le.mpr
    intro U hU z
    let U' : unitary (E →L[ℂ] E) :=
      ⟨(U : E →L[ℂ] E), Unitary.map_mem M.commutant.toStarSubalgebra.subtype hU⟩
    obtain ⟨hD, hC⟩ := hH U' U.property
    exact H.mem_graph_iff.mpr ⟨⟨(U' : E →L[ℂ] E) z, hD z⟩, rfl, hC z⟩
  rw [CStarAlgebra.span_unitary] at hspan
  exact hspan (Submodule.mem_top : (⟨W, hW⟩ : M.commutant) ∈ ⊤) x

theorem IsAffiliated.commutes_of_mem_commutant
    {M : VonNeumannAlgebra E} {H : E →ₗ.[ℂ] E} (hH : IsAffiliated M H)
    {W : E →L[ℂ] E} (hW : W ∈ M.commutant) :
    ∃ hD : ∀ x : H.domain, W (x : E) ∈ H.domain,
      ∀ x : H.domain, H ⟨W (x : E), hD x⟩ = W (H x) := by
  let hD : ∀ x : H.domain, W (x : E) ∈ H.domain := fun x =>
    H.mem_domain_of_mem_graph (hH.graph_mem_of_mem_commutant hW x)
  refine ⟨hD, fun x => ?_⟩
  exact H.mem_graph_snd_inj (H.mem_graph ⟨W x, hD x⟩)
    (hH.graph_mem_of_mem_commutant hW x) rfl

theorem IsAffiliated.transported_projection_mem
    {M : VonNeumannAlgebra E} {H : E →ₗ.[ℂ] E} (hH : IsAffiliated M H)
    {p : E →L[ℂ] E} (hpM : p ∈ M) (hp : IsStarProjection p) :
    (InvariantRotation.AffiliatedTransport.transported H p.range).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  obtain ⟨hD, hC⟩ := hH.commutes_of_mem_commutant hW
  have hpW := (VonNeumannAlgebra.IsStarProjection.mem_iff hp M).mp hpM W hW
  exact InvariantRotation.AffiliatedTransport.transported_invariant_of_commutes H p.range W
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hpW)
    (fun x hx => hD ⟨x, hx⟩) hC

theorem IsAffiliated.transported_projection_invariant
    {M : VonNeumannAlgebra E} {H : E →ₗ.[ℂ] E} (hH : IsAffiliated M H)
    (A B : E →L[ℂ] E)
    (hD : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hD x⟩ = B (H x))
    {p : E →L[ℂ] E} (hpM : p ∈ M) (hp : IsStarProjection p)
    (hinv : (1 - p) * A * p = 0) :
    let Q := (InvariantRotation.AffiliatedTransport.transported H p.range).starProjection
    Q ∈ M ∧ IsStarProjection Q ∧ (1 - Q) * B * Q = 0 := by
  dsimp only
  refine ⟨hH.transported_projection_mem hpM hp, isStarProjection_starProjection, ?_⟩
  have hpap : p * A * p = A * p := by
    rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hinv
    exact hinv.symm
  have hpA : p.range ∈ Module.End.invtSubmodule A := by
    apply (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
      hp.isIdempotentElem).mpr
    exact hpap
  have hQB := InvariantRotation.AffiliatedTransport.transported_invariant H p.range A B
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hpA)
    (fun x hx => hD ⟨x, hx⟩) hI
  have hQinv :
      (InvariantRotation.AffiliatedTransport.transported H p.range).starProjection.range ∈
        Module.End.invtSubmodule B := by
    rw [Submodule.range_starProjection]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr hQB
  have hQBQ := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    isStarProjection_starProjection.isIdempotentElem).mp hQinv
  simp only [← ContinuousLinearMap.mul_def] at hQBQ
  rw [sub_mul, one_mul, sub_mul, mul_assoc, hQBQ, sub_self]

end Invariant233

end

end OAI
