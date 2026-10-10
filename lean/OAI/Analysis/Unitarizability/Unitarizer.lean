import OAI.Analysis.Unitarizability.Triangular
import OAI.Analysis.Unitarizability.InvariantProjection

namespace OAI

/-! The bounded implementer forced by a unitarizing similarity.
The commuting projection onto H ⊕ 0 has upper-right block equal to the
negative implementer, avoiding a bounded inverse for graph coordinates. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A global cocycle implementer obtained from the similarity itself. -/
theorem implementer_of_similar (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by
  let π := representation U D h1 hD
  let M : ClosedSubmodule ℂ (Double H) :=
    ⟨(WithLp.sndL 2 ℂ H H).ker, (WithLp.sndL 2 ℂ H H).isClosed_ker⟩
  have hM : ∀ g x, x ∈ M → π g x ∈ M := by
    intro g x hx
    change x.snd = 0 at hx
    change (operator (U g) (D g) x).snd = 0
    simp [hx]
  rcases InvariantProjection.exists_commuting_projection π hπ M hM with ⟨P, hm, hf, hp⟩
  let q : H →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp (P.comp inr)
  have hzero (x : Double H) : (P x).snd = 0 := hm x
  have hfix (x : H) : P (inl x) = inl x := hf _ (by change (inl x).snd = 0; simp)
  have hdecomp (x : Double H) : x = inl x.fst + inr x.snd := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp
  have hfst (x : Double H) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q]
  refine ⟨-q, ?_⟩
  intro g
  ext x
  have h := congrArg (fun T : Double H →L[ℂ] Double H => (T (inr (U g⁻¹ x))).fst) (hp g).eq
  change (P (operator (U g) (D g) (inr (U g⁻¹ x)))).fst =
    (operator (U g) (D g) (P (inr (U g⁻¹ x)))).fst at h
  rw [hfst, operator_fst, operator_snd, operator_fst, hzero] at h
  have hinv : U g (U g⁻¹ x) = x := InvariantProjection.rep_inv U g x
  simp only [inr_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, zero_add, hinv,
    add_zero] at h
  change D g x = (-q) x - U g ((-q) (U g⁻¹ x))
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  change D g x + q x = U g (q (U g⁻¹ x)) at h
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end Triangular
end Dixmier

end

end OAI
