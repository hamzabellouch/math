import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.FgMatrixRing

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_finite_padic_matrix_model {G n : Type} [Group G] [Group.FG G]
    [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]
    (ρ : G →* GL n (AlgebraicClosure (Padic p)))
    (E : Finset (AlgebraicClosure (Padic p))) :
    ∃ L : IntermediateField (Padic p) (AlgebraicClosure (Padic p)),
      FiniteDimensional (Padic p) L ∧ (E:Set (AlgebraicClosure (Padic p)))⊆(L:Set (AlgebraicClosure (Padic p))) ∧
      ∃ τ : G →* GL n L, ∀ g,
        Matrix.GeneralLinearGroup.map L.val.toRingHom (τ g)=ρ g := by
  obtain ⟨D,hD,hm⟩ := LinearGrowth.exists_finiteType_matrix_ring ρ
  obtain ⟨F,hF⟩ := (Subalgebra.fg_iff_finiteType D).mpr hD
  let L := IntermediateField.adjoin (Padic p) (↑(F∪E):Set (AlgebraicClosure (Padic p)))
  have hfin : FiniteDimensional (Padic p) L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hDL : D≤L.toSubalgebra.restrictScalars ℤ := by
    rw [←hF]
    apply Algebra.adjoin_le
    intro x hx
    exact IntermediateField.subset_adjoin (Padic p) _ (Finset.mem_union_left _ hx)
  let τ : G →* GL n L := LinearGrowth.liftMatrixGroup ρ
    (L.toSubalgebra.restrictScalars ℤ) (fun g i j => hDL (hm g i j))
  refine ⟨L,hfin,?_,τ,?_⟩
  · intro x hx
    exact IntermediateField.subset_adjoin (Padic p) _ (Finset.mem_union_right _ hx)
  · intro g
    exact LinearGrowth.liftMatrixGroup_map ρ (L.toSubalgebra.restrictScalars ℤ) _ g

end CriticalPercolation.Arithmetic
end
end

end OAI
