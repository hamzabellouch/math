import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace OAI

/-! # Finite dimension from a bound on independent generators -/

open Set Module
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem finite_span_of_independent_bound (K : Set E) (n : ℕ)
    (hspan : Submodule.span ℝ K = ⊤)
    (hno : ∀ v : Fin (n+1) → E, (∀ i, v i ∈ K) → ¬LinearIndependent ℝ v) :
    FiniteDimensional ℝ E ∧ Module.finrank ℝ E ≤ n := by
  classical
  let I := ↥((linearIndepOn_empty ℝ (id : E → E)).extend (empty_subset K))
  let B : Basis I ℝ E := Basis.ofSpan hspan.ge
  have hBK (i : I) : B i ∈ K := Basis.ofSpan_subset hspan.ge ⟨i,rfl⟩
  have hbad (e : Fin (n+1) ↪ I) : False :=
    hno (fun i => B (e i)) (fun i => hBK (e i)) (B.linearIndependent.comp e e.injective)
  have hfinite : Finite I := by
    by_contra h
    let : Infinite I := not_finite_iff_infinite.mp h
    exact hbad (Fin.valEmbedding.trans (Infinite.natEmbedding I))
  let := hfinite
  let := Fintype.ofFinite I
  have hcard : Fintype.card I ≤ n := by
    by_contra h
    have hle : Fintype.card (Fin (n+1)) ≤ Fintype.card I := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
    exact hbad e
  have hfin : FiniteDimensional ℝ E := Module.Finite.of_basis B
  refine ⟨hfin,?_⟩
  rw [Module.finrank_eq_card_basis B]
  exact hcard

end RegularPointCoordinates

end

end OAI
