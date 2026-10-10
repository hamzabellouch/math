import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorSubalgebras
import OAI.Analysis.WeakInfiniteness.UnitizationTensor

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped TensorProduct ComplexOrder ENNReal

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def unitizationCharacter : Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ A
  map_star' _ := rfl

def unitizationScalarEnd : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ A :=
  (StarAlgHom.ofId ℂ (Unitization ℂ A)).comp unitizationCharacter

lemma unitizationScalarEnd_apply (a : Unitization ℂ A) :
    unitizationScalarEnd a=a.fst • (1 : Unitization ℂ A) :=
  by
    change algebraMap ℂ (Unitization ℂ A) a.fst=a.fst • (1 : Unitization ℂ A)
    exact Algebra.algebraMap_eq_smul_one _

lemma unitization_difference_scalarEnd (a : Unitization ℂ A) :
    a-unitizationScalarEnd a=(a.snd : Unitization ℂ A) := by
  change a-algebraMap ℂ (Unitization ℂ A) a.fst=(a.snd : Unitization ℂ A)
  apply Unitization.ext
  · change a.fst-a.fst=0
    exact sub_self _
  · change a.snd-0=a.snd
    exact sub_zero _

lemma minimalMapLeft_scalarEnd_elementary (a : Unitization ℂ A) (c : C) :
    minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom (minimalElementary a c)=
      rightElementaryHom (a.fst • c) := by
  rw [minimalMapLeft_elementary]
  apply Subtype.ext
  change spatialElementary (unitizationScalarEnd a) c=spatialElementary 1 (a.fst • c)
  rw [unitizationScalarEnd_apply, spatialElementary_smul_left, spatialElementary_smul_right]

lemma difference_scalarEnd_elementary (a : Unitization ℂ A) (c : C) :
    minimalElementary a c-
        minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom (minimalElementary a c)=
      minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) (minimalElementary a.snd c) := by
  rw [minimalMapLeft_elementary, minimalMapLeft_elementary]
  apply Subtype.ext
  change spatialElementary a c-spatialElementary (unitizationScalarEnd a) c=
    spatialElementary (a.snd : Unitization ℂ A) c
  have h := spatialElementary_add_left (a-unitizationScalarEnd a) (unitizationScalarEnd a) c
  rw [sub_add_cancel, unitization_difference_scalarEnd] at h
  exact sub_eq_iff_eq_add.mpr h

lemma unitizationTensor_decomposition (z : MinimalTensor (Unitization ℂ A) C) :
    ∃ (z₀ : MinimalTensor A C) (c : C),
      z-minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z=
        minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) z₀ ∧
      minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z=rightElementaryHom c := by
  let P := minimalMapLeft (C := C) (unitizationScalarEnd (A := A)).toNonUnitalStarAlgHom
  let i := minimalMapLeft (C := C) (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let r := rightElementaryHom (A := Unitization ℂ A) (C := C)
  let L : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C :=
    LinearMap.id-(P : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  have hL : Continuous L := continuous_id.sub (nonUnitalStarHom_continuous P)
  let R := LinearMap.range (i : MinimalTensor A C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  let S := R.comap L
  have hS : IsClosed (S : Set (MinimalTensor (Unitization ℂ A) C)) :=
    (nonUnitalStarHom_isClosed_range i).preimage hL
  have hz₀ : L z∈R := minimalTensor_closed_submodule S hS (by
    intro a c
    exact ⟨minimalElementary a.snd c, (difference_scalarEnd_elementary a c).symm⟩) z
  obtain ⟨z₀,hz₀⟩ := hz₀
  let R' := LinearMap.range (r : C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  let S' := R'.comap (P : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  have hS' : IsClosed (S' : Set (MinimalTensor (Unitization ℂ A) C)) :=
    (nonUnitalStarHom_isClosed_range r).preimage (nonUnitalStarHom_continuous P)
  have hcz : P z∈R' := minimalTensor_closed_submodule S' hS' (by
    intro a c
    exact ⟨a.fst • c, (minimalMapLeft_scalarEnd_elementary a c).symm⟩) z
  obtain ⟨c,hc⟩ := hcz
  exact ⟨z₀,c,hz₀.symm,hc.symm⟩

lemma minimalMapRight_rightElementary {E : Type u} [CStarAlgebra E]
    (q : C →⋆ₙₐ[ℂ] D) (c : C) :
    minimalMapRight q (rightElementaryHom (A := E) c)=rightElementaryHom (q c) := rfl

lemma mapLeft_tensorKernel {B : Type u} [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) {x : SpatialAmbient A C}
    (hx : x∈tensorKernelIdeal (A := A) q) :
    spatialMapLeft φ x∈tensorKernelIdeal (A := B) q := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapLeft φ) (tensorKernelIdeal (A := B) q))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hx
  · rintro _ ⟨a,c,hc,rfl⟩
    change spatialMapLeft φ (spatialElementary a c)∈tensorKernelIdeal (A := B) q
    rw [spatialMapLeft_elementary]
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨φ a,c,hc,rfl⟩
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapLeft φ))

theorem exact_unitization (hA : Exact A) : Exact (Unitization ℂ A) := by
  intro C D _ _ q hq z hz
  have hzq : minimalMapRight q z=0 := (minimalMapRight_eq_zero_iff q z).mpr hz
  obtain ⟨z₀,c,hz₀,hc⟩ := unitizationTensor_decomposition z
  have hPq : minimalMapRight q (minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z)=0 := by
    rw [minimalMapLeft_right_commute, hzq, map_zero]
  have hqc : q c=0 := by
    apply (rightElementaryHom_injective (E := Unitization ℂ A))
    rw [map_zero, ← minimalMapRight_rightElementary, ← hc, hPq]
  have hz₀q : minimalMapRight q z₀=0 := by
    apply minimalMapLeft_injective (Unitization.inrNonUnitalStarAlgHom ℂ A) Unitization.inr_injective
    rw [map_zero, ← minimalMapLeft_right_commute, ← hz₀, map_sub, hzq, hPq, sub_self]
  have hz₀mem := hA C D q hq z₀ ((minimalMapRight_eq_zero_iff q z₀).mp hz₀q)
  have hz' : z=minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) z₀+rightElementaryHom c := by
    rw [← hz₀, ← hc, sub_add_cancel]
  rw [hz']
  apply (tensorKernelIdeal (A := Unitization ℂ A) q).add_mem
  · exact mapLeft_tensorKernel (Unitization.inrNonUnitalStarAlgHom ℂ A) q hz₀mem
  · apply NonUnitalStarSubalgebra.le_topologicalClosure
    exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨1,c,hqc,rfl⟩

end

end WeakPureInfiniteness
end

end OAI
