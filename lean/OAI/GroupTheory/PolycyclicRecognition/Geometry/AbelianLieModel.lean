import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace OAI

/-! # The abelian base case of nilpotent Lie model existence

An abelian real Lie algebra is integrated by its additive vector group.
The equivalence below identifies the actual invariant-vector-field bracket.
-/

noncomputable section
namespace PolycyclicRecognition

open VectorField
open scoped Manifold

variable {V : Type*} [RealNormedLieAlgebra V]

local instance vectorGroupChartedSpace : ChartedSpace V (Multiplicative V) :=
  inferInstanceAs (ChartedSpace V V)

local instance vectorGroupLieGroup : LieGroup (𝓘(ℝ, V)) ⊤ (Multiplicative V) where
  toIsManifold := by change IsManifold (𝓘(ℝ, V)) ⊤ V; infer_instance
  contMDiff_mul := by
    change ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, V)) ⊤
      (fun p : V × V => p.1 + p.2)
    exact contMDiff_add (I := 𝓘(ℝ, V)) (n := ⊤)
  contMDiff_inv := by
    change ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ⊤ (fun v : V => -v)
    exact contDiff_neg.contMDiff

theorem vectorGroup_invariantField
    (v : GroupLieAlgebra (𝓘(ℝ, V)) (Multiplicative V)) (g : Multiplicative V) :
    mulInvariantVectorField v g = v := by
  change mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, V)) (fun x : V => g.toAdd + x) 0 v = v
  have hd : HasFDerivAt (fun x : V => g.toAdd + x) (ContinuousLinearMap.id ℝ V) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : V)).const_add g.toAdd
  exact congrArg (fun A : V →L[ℝ] V => A (v : V)) hd.hasMFDerivAt.mfderiv

theorem vectorGroup_bracket
    (v w : GroupLieAlgebra (𝓘(ℝ, V)) (Multiplicative V)) : ⁅v, w⁆ = 0 := by
  rw [GroupLieAlgebra.bracket_def]
  have hv : mulInvariantVectorField v = (fun _ : Multiplicative V => v) :=
    funext (vectorGroup_invariantField v)
  have hw : mulInvariantVectorField w = (fun _ : Multiplicative V => w) :=
    funext (vectorGroup_invariantField w)
  rw [hv, hw]
  have hconst (x y : V) :
      lieBracketWithin ℝ (fun _ : V => x) (fun _ : V => y) Set.univ 0 = 0 := by
    simp [lieBracketWithin]
  exact (congrFun (mlieBracketWithin_eq_lieBracketWithin
    (V := fun _ : V => v) (W := fun _ : V => w) (s := Set.univ)) (0 : V)).trans (hconst v w)

variable [FiniteDimensional ℝ V] [IsLieAbelian V]

/-- The additive group, equipped with its actual tangent Lie algebra. -/
def abelianLieModel : NilpotentLieModel V := by
  let : MeasurableSpace (Multiplicative V) := borel _
  let : BorelSpace (Multiplicative V) := ⟨rfl⟩
  let : SimplyConnectedSpace (Multiplicative V) :=
    inferInstanceAs (SimplyConnectedSpace V)
  exact
    { modelSpace := V
      carrier := Multiplicative V
      equiv :=
        { LinearEquiv.refl ℝ V with
          map_lie' := by
            intro x y
            have hzero : ⁅x, y⁆ = (0 : V) := LieModule.IsTrivial.trivial x y
            exact hzero.trans (vectorGroup_bracket (V := V) x y).symm } }

/-- No Lie-existence hypothesis is needed in the abelian base case. -/
theorem nilpotentLieExistenceInput_of_abelian
    (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] [IsLieAbelian L] :
    NilpotentLieExistenceInput L := by
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  intro _
  exact ⟨abelianLieModel (V := L)⟩

end PolycyclicRecognition

end

end OAI
