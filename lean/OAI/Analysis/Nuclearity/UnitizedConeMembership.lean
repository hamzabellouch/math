import OAI.Analysis.Nuclearity.UnitizedCoefficientConvexity
import OAI.Analysis.Nuclearity.UnitizedCoefficientMaps

namespace OAI

/-! Concrete members of the coefficient cone, with arbitrary finite index
sets reindexed to its finite arrays. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [Fintype I]
  (U : Ultrafilter ℕ)

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

omit [PartialOrder B] in
lemma unitizedCoefficientEnlargement_equiv {J : Type*} [Fintype J]
    (e : J ≃ I) (T : B → N) (a : I → Unitization ℂ N) (c : I → B) (b : B) :
    unitizedCoefficientEnlargement T (a ∘ e) (c ∘ e) b =
      unitizedCoefficientEnlargement T a c b := by
  unfold unitizedCoefficientEnlargement
  simp only [Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (fun j => e.sum_comp
    (fun i => unitizedSandwich (a (e j)) (T (star (c (e j)) * b * c i)) (a i)))

lemma coefficient_enlargement_mem_cone (β : B →⋆ₙₐ[ℂ] N)
    (T : B →L[ℂ] N) (hi : ApproximatelyInnerAlong β T)
    (hp : ∀ b, 0 ≤ b → 0 ≤ T b) (hc : ∀ b c, Commute (T b) (T c))
    (a : I → Unitization ℂ N) (c : I → B) :
    unitizedCoefficientEnlargement T a c ∈ finiteUnitizedAbelianCoefficientCone U β := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨1, Fintype.card I, (fun _ => T), (fun _ => hi), (fun _ => hp),
    (fun _ => hc), (fun p => a (e p.2)), (fun p => c (e p.2)), ?_⟩
  intro b
  simp only [Fin.sum_univ_one]
  exact (unitizedCoefficientEnlargement_equiv U e T a c b).symm

variable [StarOrderedRing B]

lemma coefficient_inner_mem_cone (β : B →⋆ₙₐ[ℂ] N) (v : N)
    (hc : ∀ b c, Commute (innerHomCompression β v b) (innerHomCompression β v c))
    (a : I → Unitization ℂ N) (c : I → B) :
    (innerHomCompression β (∑ i, unitizedRightMul (β (c i) * v) (a i)) : B → N) ∈
      finiteUnitizedAbelianCoefficientCone U β := by
  have hi : ApproximatelyInnerAlong β (innerHomCompression β v) := by
    intro F ε hε
    exact ⟨1, fun _ => v, fun b _ => by simpa only [Fin.sum_univ_one,
      innerHomCompression_apply, sub_self, norm_zero] using hε⟩
  have hp : ∀ b, 0 ≤ b → 0 ≤ innerHomCompression β v b :=
    fun b hb => star_left_conjugate_nonneg (map_nonneg β hb) v
  have he : (innerHomCompression β (∑ i, unitizedRightMul (β (c i) * v) (a i)) : B → N) =
      unitizedCoefficientEnlargement (innerHomCompression β v) a c := by
    funext b
    exact (unitizedCoefficientEnlargement_inner β a c v b).symm
  rw [he]
  exact coefficient_enlargement_mem_cone U β _ hi hp hc a c

end WeakPureInfiniteness

end

end OAI
