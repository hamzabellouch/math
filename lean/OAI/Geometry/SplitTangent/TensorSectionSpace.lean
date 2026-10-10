import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.TwistedCurveTensor

namespace OAI

/-! Tensor Section Space. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

@[simp] lemma tangentTensorCoordinates_zero {X : ComplexManifold.{u}} {m : ℕ}
    (g : ℂ → X.Carrier) (z₀ : ℂ) :
    tangentTensorCoordinates (m := m) g 0 z₀=0 := by
  ext z v
  rfl

@[simp] lemma tangentTensorCoordinates_add {X : ComplexManifold.{u}} {m : ℕ}
    (g : ℂ → X.Carrier) (A B : ℂ → TangentTensor X m) (z₀ : ℂ) :
    tangentTensorCoordinates g (A+B) z₀=
      tangentTensorCoordinates g A z₀+tangentTensorCoordinates g B z₀ := by
  ext z v
  rfl

@[simp] lemma tangentTensorCoordinates_smul {X : ComplexManifold.{u}} {m : ℕ}
    (g : ℂ → X.Carrier) (c : ℂ) (A : ℂ → TangentTensor X m) (z₀ : ℂ) :
    tangentTensorCoordinates g (c • A) z₀=c • tangentTensorCoordinates g A z₀ := by
  ext z v
  rfl

 
def tensorSectionSpace {X : ComplexManifold.{u}} (g : RationalCurve X) (d : ℤ) (m : ℕ) :
    Submodule ℂ ((ℂ → TangentTensor X m) × (ℂ → TangentTensor X m)) where
  carrier := {A | (∀z,AnalyticAt ℂ (tangentTensorCoordinates g.finite A.1 z) z) ∧
    (∀z,AnalyticAt ℂ (tangentTensorCoordinates g.infinity A.2 z) z) ∧
    ∀z : ℂ,z≠0 → A.1 z=z^d • A.2 z⁻¹}
  zero_mem' := by
    refine ⟨fun z => ?_,fun z => ?_,fun z hz => ?_⟩
    · simp only [Prod.fst_zero,tangentTensorCoordinates_zero]
      change AnalyticAt ℂ (fun _ : ℂ => (0 : TangentTensor X m)) z
      exact analyticAt_const
    · simp only [Prod.snd_zero,tangentTensorCoordinates_zero]
      change AnalyticAt ℂ (fun _ : ℂ => (0 : TangentTensor X m)) z
      exact analyticAt_const
    · simp
  add_mem' := by
    intro A B hA hB
    refine ⟨fun z => ?_,fun z => ?_,fun z hz => ?_⟩
    · simpa using (hA.1 z).add (hB.1 z)
    · simpa using (hA.2.1 z).add (hB.2.1 z)
    · change A.1 z+B.1 z=z^d • (A.2 z⁻¹+B.2 z⁻¹)
      rw [hA.2.2 z hz,hB.2.2 z hz,smul_add]
  smul_mem' := by
    intro c A hA
    refine ⟨fun z => ?_,fun z => ?_,fun z hz => ?_⟩
    · simpa using (hA.1 z).const_smul (c := c)
    · simpa using (hA.2.1 z).const_smul (c := c)
    · change c • A.1 z=z^d • (c • A.2 z⁻¹)
      rw [hA.2.2 z hz,smul_comm]

namespace tensorSectionSpace
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {d : ℤ} {m : ℕ}

def toTensor (A : tensorSectionSpace g d m) : TwistedCurveTensor g d m where
  finite := A.val.1
  infinity := A.val.2
  finite_holomorphic := A.property.1
  infinity_holomorphic := A.property.2.1
  overlap := A.property.2.2

 
def contract (σ : Fin m → CurveTangentSection g) :
    tensorSectionSpace g d m →ₗ[ℂ] DiagonalRationality.lineSections d where
  toFun A := (toTensor A).contract σ
  map_add' A B := by
    apply DiagonalRationality.lineSections_ext
    rfl
  map_smul' c A := by
    apply DiagonalRationality.lineSections_ext
    rfl

end tensorSectionSpace

 

def symmetricSupportedTensors {X : ComplexManifold.{u}} (g : RationalCurve X)
    (S : TangentSplitting X) (d : ℤ) (m : ℕ) : Submodule ℂ (tensorSectionSpace g d m) where
  carrier := {A | (∀z v,A.val.1 z (fun i => S.projector (g.finite z) (v i))=A.val.1 z v) ∧
    (∀z v,A.val.2 z (fun i => S.projector (g.infinity z) (v i))=A.val.2 z v) ∧
    (∀z v (p : Equiv.Perm (Fin m)),A.val.1 z (v ∘ p)=A.val.1 z v) ∧
    (∀z v (p : Equiv.Perm (Fin m)),A.val.2 z (v ∘ p)=A.val.2 z v)}
  zero_mem' := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨fun z v => ?_,fun z v => ?_,fun z v p => ?_,fun z v p => ?_⟩
    · change A.val.1 z _+B.val.1 z _=A.val.1 z v+B.val.1 z v
      rw [hA.1,hB.1]
    · change A.val.2 z _+B.val.2 z _=A.val.2 z v+B.val.2 z v
      rw [hA.2.1,hB.2.1]
    · change A.val.1 z _+B.val.1 z _=A.val.1 z v+B.val.1 z v
      rw [hA.2.2.1,hB.2.2.1]
    · change A.val.2 z _+B.val.2 z _=A.val.2 z v+B.val.2 z v
      rw [hA.2.2.2,hB.2.2.2]
  smul_mem' := by
    intro c A hA
    refine ⟨fun z v => ?_,fun z v => ?_,fun z v p => ?_,fun z v p => ?_⟩
    · change c • A.val.1 z _=c • A.val.1 z v
      rw [hA.1]
    · change c • A.val.2 z _=c • A.val.2 z v
      rw [hA.2.1]
    · change c • A.val.1 z _=c • A.val.1 z v
      rw [hA.2.2.1]
    · change c • A.val.2 z _=c • A.val.2 z v
      rw [hA.2.2.2]

namespace PointedGenerated
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {S : TangentSplitting X}

theorem exists_basis_sections (h : PointedGenerated g S.first) :
    ∃σ : Fin (Module.finrank ℂ (S.first (g.finite 1))) → CurveTangentSection g,
      (∀j z,(σ j).finite z∈S.first (g.finite z)) ∧
      (∀j z,(σ j).infinity z∈S.first (g.infinity z)) ∧
      (∀j,(σ j).finite 0=0) ∧
      ∀v∈S.first (g.finite 1),∃a : Fin (Module.finrank ℂ (S.first (g.finite 1))) → ℂ,
        ∑j,a j • (σ j).finite 1=v := by
  classical
  let : FiniteDimensional ℂ (Tangent X (g.finite 1)) :=
    inferInstanceAs (FiniteDimensional ℂ (Model X))
  let b := Module.finBasis ℂ (S.first (g.finite 1))
  choose σ hσf hσi hσ0 hσ1 using fun j => h (b j).val (b j).property
  refine ⟨σ,hσf,hσi,hσ0,?_⟩
  intro v hv
  refine ⟨fun j => b.repr ⟨v,hv⟩ j,?_⟩
  simpa only [hσ1,Submodule.coe_sum,Submodule.coe_smul] using
    congrArg Subtype.val (b.sum_repr ⟨v,hv⟩)

end PointedGenerated
end SplitTangent

end

end OAI
