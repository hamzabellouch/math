import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraTangentSolvable
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # The Lie algebra of an actual solvable Lie group

The intrinsic adjoint exponential puts the adjoint representation into the
infinitesimal action of a solvable matrix group. Its derived series vanishes;
one additional bracket kills the central kernel of the adjoint action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Group.IsSolvable G]

/-- Group solvability implies solvability of the intrinsic tangent Lie algebra. -/
theorem groupLieAlgebra_isSolvable :
    LieAlgebra.IsSolvable (GroupLieAlgebra (𝓘(ℝ, E)) G) := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let A := E →L[ℝ] E
  let ρ : G →* Aˣ := (conjugationDifferentialHom (E := E) (G := G)).toHomUnits
  let R := algebraGroupTangentLie ρ.range
  let : Group.IsSolvable ρ.range :=
    Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  let : LieAlgebra.IsSolvable R := algebraGroupTangentLie_isSolvable ρ.range
  let j₀ : L →ₗ⁅ℝ⁆ A :=
    { toLinearMap :=
        { toFun := groupAdjointOperator
          map_add' := by
            intro x y
            ext z
            exact congrArg (fun w : L => (w : E)) (add_lie x y (show L from z))
          map_smul' := by
            intro r x
            ext z
            exact congrArg (fun w : L => (w : E)) (smul_lie r x (show L from z)) }
      map_lie' := by
        intro x y
        ext z
        exact congrArg (fun w : L => (w : E)) (lie_lie x y (show L from z)) }
  have hmem (v : L) : j₀ v ∈ R := by
    apply Submodule.subset_span
    let Exp := groupExponential (E := E) (G := G)
    have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
    refine ⟨fun t => ρ (Exp (t • v)), fun t => ⟨Exp (t • v), rfl⟩, ?_, ?_⟩
    · change ρ (Exp (0 • v)) = 1
      rw [zero_smul, hExp.map_zero, map_one]
    · have h := hasDerivAt_exp_smul_const (j₀ v) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
      convert h using 1
      funext t
      exact adjointLinearMap_exponential hExp v t
  let j : L →ₗ⁅ℝ⁆ R :=
    { toFun := fun x => ⟨j₀ x, hmem x⟩
      map_add' := fun x y => Subtype.ext (j₀.map_add x y)
      map_smul' := fun r x => Subtype.ext (j₀.map_smul r x)
      map_lie' := fun {x y} => Subtype.ext (j₀.map_lie x y) }
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable ℝ R
  have hjzero (x : L) (hx : x ∈ LieAlgebra.derivedSeries ℝ L n) : j x = 0 := by
    have hm := LieIdeal.derivedSeries_map_le (f := j) n (LieIdeal.mem_map hx)
    rwa [hn] at hm
  apply (LieAlgebra.isSolvable_iff ℝ L).mpr
  refine ⟨n + 1, le_antisymm ?_ bot_le⟩
  have hz : (LieAlgebra.derivedSeries ℝ L (n + 1)).toSubmodule ≤ ⊥ := by
    rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieSubmodule.lieIdeal_oper_eq_linear_span']
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, _, rfl⟩
    change ⁅x, y⁆ = 0
    have hzero : j₀ x = 0 := congrArg Subtype.val (hjzero x hx)
    exact congrArg (fun f : A => f y) hzero
  exact hz

end PolycyclicRecognition

end

end OAI
