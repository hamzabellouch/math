import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeAbelianDuality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteDimensionTorsionFree
import Mathlib.LinearAlgebra.FreeModule.PID

namespace OAI

/-! # Uniform rank bounds on finitely generated abelian subgroups

A torsion-free finitely generated abelian group is an integral lattice. The
explicit lattice duality calculation therefore bounds the rank of every such
subgroup by a common ambient cohomological-dimension bound.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A]

def integralLatticeEquivOfBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Additive A)) :
    IntegralLatticeGroup n ≃* A where
  toFun a := Additive.toMul (b.equivFun.symm a.toAdd)
  invFun a := Multiplicative.ofAdd (b.equivFun (Additive.ofMul a))
  left_inv a := by
    change Multiplicative.ofAdd (b.equivFun (b.equivFun.symm a.toAdd)) = a
    rw [LinearEquiv.apply_symm_apply]
    rfl
  right_inv a := by
    change Additive.toMul (b.equivFun.symm (b.equivFun (Additive.ofMul a))) = a
    rw [LinearEquiv.symm_apply_apply]
    rfl
  map_mul' a b' := congrArg Additive.toMul (b.equivFun.symm.map_add a.toAdd b'.toAdd)

theorem exists_integralLattice_equiv [Group.FG A] (hA : HasNoNontrivialTorsion A) :
    ∃ n, Nonempty (IntegralLatticeGroup n ≃* A) := by
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro a ha hf
    exact ha (hA a (orderOf a) (ne_of_gt hf.orderOf_pos) (pow_orderOf_eq_one a)))
  let : IsAddTorsionFree (Additive A) := inferInstance
  let : Module.IsTorsionFree ℤ (Additive A) := inferInstance
  have hM : Module.Finite ℤ (Additive A) := by
    obtain ⟨s, hs, hfin⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG (Additive A))
    apply Module.Finite.of_fg_top
    refine Submodule.fg_def.mpr ⟨s, hfin, ?_⟩
    apply AddSubgroup.toIntSubmodule.symm.injective
    simpa only [AddSubgroup.toIntSubmodule_symm, Submodule.span_int_eq_addSubgroupClosure, Submodule.top_toAddSubgroup] using hs
  let := hM
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive A)
  exact ⟨n, ⟨integralLatticeEquivOfBasis b⟩⟩

theorem abelian_subgroup_lattice_rank_bound {G : Type} [Group G]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] [Group.FG H] :
    ∃ n ≤ d, Nonempty (IntegralLatticeGroup n ≃* H) := by
  have hH : HasFiniteIntegralCohomologicalDimension H :=
    ⟨d, subgroup_cohomologicalDimension_le H d⟩
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv hH.torsionFree
  exact ⟨n, lattice_rank_le_cohomologicalDimension d n
    (H.subtype.comp e.toMonoidHom) (Subtype.val_injective.comp e.injective), ⟨e⟩⟩

end PolycyclicRecognition

end

end OAI
