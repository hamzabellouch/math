import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace OAI

/-! # The integral vector lattice as a solvable Lie lattice

This constructs the abelian case of the lattice-realization input. The compact
fundamental cover is the closed unit parallelepiped of the standard real basis.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

def vectorSolvableLieModel (n : ℕ) : SimplyConnectedSolvableLieModel := by
  let V := Fin n → ℝ
  let : ChartedSpace V (Multiplicative V) := inferInstanceAs (ChartedSpace V V)
  let : LieGroup (𝓘(ℝ, V)) ⊤ (Multiplicative V) :=
    { toIsManifold := by change IsManifold (𝓘(ℝ, V)) ⊤ V; infer_instance
      contMDiff_mul := by
        change ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, V)) ⊤
          (fun p : V × V => p.1 + p.2)
        exact contMDiff_add (I := 𝓘(ℝ, V)) (n := ⊤)
      contMDiff_inv := by
        change ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ⊤ (fun v : V => -v)
        exact contDiff_neg.contMDiff }
  let : SimplyConnectedSpace (Multiplicative V) := inferInstanceAs (SimplyConnectedSpace V)
  exact { modelSpace := V, carrier := Multiplicative V }

def standardVectorLattice (n : ℕ) : Subgroup (vectorSolvableLieModel n).carrier :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup.toSubgroup

theorem standardVectorLattice_uniform (n : ℕ) : IsUniformLattice (standardVectorLattice n) := by
  let b := Pi.basisFun ℝ (Fin n)
  let L := Submodule.span ℤ (Set.range b)
  change IsUniformLattice (G := Multiplicative (Fin n → ℝ)) L.toAddSubgroup.toSubgroup
  have hdisc : DiscreteTopology (standardVectorLattice n) :=
    inferInstanceAs (DiscreteTopology L)
  let K : Set (Fin n → ℝ) := parallelepiped b
  have hK : IsCompact K := b.parallelepiped.isCompact
  refine ⟨hdisc, K, hK, ?_⟩
  intro g
  let z := ZSpan.floor b g.toAdd
  refine ⟨⟨Multiplicative.ofAdd (z : Fin n → ℝ), z.property⟩,
    Multiplicative.ofAdd (ZSpan.fract b g.toAdd), ?_, ?_⟩
  · exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b g.toAdd)
  · change (z : Fin n → ℝ) + ZSpan.fract b g.toAdd = g.toAdd
    dsimp only [z, ZSpan.fract]
    abel

def standardVectorLatticeEquiv (n : ℕ) :
    IntegralLatticeGroup n ≃* standardVectorLattice n := by
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
  let b := IsZLattice.basis L
  exact
    { toFun := fun a => ⟨Multiplicative.ofAdd (b.equivFun.symm a.toAdd : Fin n → ℝ),
        (b.equivFun.symm a.toAdd).property⟩
      invFun := fun a => Multiplicative.ofAdd (b.equivFun ⟨a.val.toAdd, a.property⟩)
      left_inv := by
        intro a
        change Multiplicative.ofAdd (b.equivFun (b.equivFun.symm a.toAdd)) = a
        rw [LinearEquiv.apply_symm_apply]
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        change Multiplicative.ofAdd
          (b.equivFun.symm (b.equivFun ⟨a.val.toAdd, a.property⟩) : Fin n → ℝ) = a.val
        rw [LinearEquiv.symm_apply_apply]
        rfl
      map_mul' := by
        intro a c
        apply Subtype.ext
        change Multiplicative.ofAdd (b.equivFun.symm (a.toAdd + c.toAdd) : Fin n → ℝ) = _
        rw [map_add]
        rfl }

theorem integralLattice_solvable_realization (n : ℕ) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (IntegralLatticeGroup n ≃* Λ) :=
  ⟨vectorSolvableLieModel n, standardVectorLattice n, standardVectorLattice_uniform n,
    ⟨standardVectorLatticeEquiv n⟩⟩

end PolycyclicRecognition

end

end OAI
