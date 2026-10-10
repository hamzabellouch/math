import Mathlib.Data.Fintype.Pi
import OAI.NumberTheory.Ostmann.Tree.ProductFibers

namespace OAI

/-!
# Uniform product fibers for a nonempty component

Fixing one distinguished leaf identifies every component-product fiber
with independent values on the remaining leaves. The fiber cardinality
therefore does not depend on its total.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def completeComponentProduct {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) (i : I) : G :=
  if h : i = i₀ then P / ∏ j, v j else v ⟨i, h⟩

theorem completeComponentProduct_pivot {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) :
    completeComponentProduct i₀ P v i₀ = P / ∏ j, v j := by
  simp [completeComponentProduct]

theorem completeComponentProduct_other {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G)
    (j : {i : I // i ≠ i₀}) : completeComponentProduct i₀ P v j = v j := by
  simp [completeComponentProduct, j.property]

theorem completeComponentProduct_total {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) :
    (∏ i : I, completeComponentProduct i₀ P v i) = P := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i₀]
  simp only [completeComponentProduct_pivot, completeComponentProduct_other, div_mul_cancel]

/-- All but one coordinate can be chosen freely in a fixed product fiber. -/
noncomputable def componentProductEquiv {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) :
    {m : I → G // ∏ i, m i = P} ≃ ({i : I // i ≠ i₀} → G) where
  toFun m j := m.1 j
  invFun v := ⟨completeComponentProduct i₀ P v, completeComponentProduct_total i₀ P v⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    change completeComponentProduct i₀ P (fun j => m.1 j) i = m.1 i
    by_cases hi : i = i₀
    · subst i
      rw [completeComponentProduct_pivot]
      have h := m.property
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i₀] at h
      calc
        _ = (m.1 i₀ * ∏ j : {i : I // i ≠ i₀}, m.1 j) /
            (∏ j : {i : I // i ≠ i₀}, m.1 j) :=
          congrArg (fun x => x / (∏ j : {i : I // i ≠ i₀}, m.1 j)) h.symm
        _ = _ := by simp
    · exact completeComponentProduct_other i₀ P (fun j => m.1 j) ⟨i, hi⟩
  right_inv v := by
    funext j
    exact completeComponentProduct_other i₀ P v j

theorem card_componentProduct {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] [Fintype G] [DecidableEq G] (i₀ : I) (P : G) :
    Fintype.card {m : I → G // ∏ i, m i = P} =
      (Fintype.card G) ^ Fintype.card {i : I // i ≠ i₀} := by
  rw [Fintype.card_congr (componentProductEquiv i₀ P), Fintype.card_fun]

theorem sum_componentProduct {I G R : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] [Fintype G] [DecidableEq G] [AddCommMonoid R]
    (i₀ : I) (P : G) (f : (I → G) → R) :
    (∑ m : {m : I → G // ∏ i, m i = P}, f m.1) =
      ∑ v : {i : I // i ≠ i₀} → G, f (completeComponentProduct i₀ P v) := by
  exact ((componentProductEquiv i₀ P).symm.bijective.sum_comp (fun m => f m.1)).symm

end Ostmann

end OAI
