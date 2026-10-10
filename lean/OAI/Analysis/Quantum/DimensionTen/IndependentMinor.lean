import Mathlib

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Arithmetic

lemma independent_minor {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Function.Surjective A.mulVec) :
    ∃ a : Fin m → Fin n, Function.Injective a ∧ (A.submatrix id a).det ≠ 0 := by
  classical
  have hsp : Submodule.span K (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr hA
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ K (Fin m → K) := Module.Basis.mk hl (by rw [hs, hsp])
  have hc : Fintype.card κ = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hh : LinearIndependent K (A.submatrix id (a ∘ e)).col := hl.comp e e.injective
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hh))

lemma restrict_rows_surjective {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0)
    (r : Fin m → Fin n) (hr : Function.Injective r) :
    Function.Surjective (A.submatrix r id).mulVec := by
  classical
  intro v
  let w : Fin n → K := Function.extend r v 0
  have hw : w ∘ r = v := Function.extend_comp hr _ _
  obtain ⟨u, hu⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))) w
  refine ⟨u, ?_⟩
  ext i
  exact (congrFun hu (r i)).trans (congrFun hw i)

end DimensionTen.Arithmetic

end
end

end OAI
