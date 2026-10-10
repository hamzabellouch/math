import OAI.Geometry.SingularHomology.HomologyConstant
import OAI.Geometry.SingularHomology.HomologyZero

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

theorem realSingularHomology_subsingleton_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    Subsingleton (RealSingularHomology n X) := by
  by_cases hn : n = 0
  · subst n
    let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
    let e := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      (ModuleCat ℝ) R (TopCat.of X)
    have hz : IsZero (∐ fun _ : X => R) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro x
      exact isEmptyElim x
    exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)
  · exact realSingularHomology_subsingleton_of_totallyDisconnected n hn X

theorem isZero_realSingularHomology_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    IsZero (RealSingularHomology n X) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (realSingularHomology_subsingleton_of_isEmpty n X)

theorem finiteDimensional_realSingularHomology_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    FiniteDimensional ℝ (RealSingularHomology n X) := by
  let := realSingularHomology_subsingleton_of_isEmpty n X
  infer_instance

theorem finiteDimensional_realSingularHomology_of_contractible
    (n : ℕ) (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    FiniteDimensional ℝ (RealSingularHomology n X) := by
  by_cases hn : n = 0
  · subst n
    exact finiteDimensional_realSingularHomologyZero X
  · let := realSingularHomology_subsingleton_of_contractible n hn X
    infer_instance

theorem realSingularHomology_finiteType_of_empty_or_contractible
    (X : Type) [TopologicalSpace X] (hX : IsEmpty X ∨ ContractibleSpace X) :
    (∀ n, FiniteDimensional ℝ (RealSingularHomology n X)) ∧
      (∀ n, 1 ≤ n → IsZero (RealSingularHomology n X)) := by
  rcases hX with hX | hX
  · let := hX
    exact ⟨fun n => finiteDimensional_realSingularHomology_of_isEmpty n X,
      fun n _ => isZero_realSingularHomology_of_isEmpty n X⟩
  · let := hX
    refine ⟨fun n => finiteDimensional_realSingularHomology_of_contractible n X,
      fun n hn => ?_⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (realSingularHomology_subsingleton_of_contractible n (by omega) X)

theorem realSingularHomologyZero_subsingleton_iff_isEmpty
    (X : Type) [TopologicalSpace X] :
    Subsingleton (RealSingularHomology 0 X) ↔ IsEmpty X := by
  constructor
  · intro h
    let := h
    exact ⟨fun x => pointHomologyClass_ne_zero x (Subsingleton.elim _ _)⟩
  · intro h
    let := h
    exact realSingularHomology_subsingleton_of_isEmpty 0 X

end Problem340

end

end OAI
