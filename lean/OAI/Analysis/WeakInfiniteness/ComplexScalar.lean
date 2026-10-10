import Mathlib
import OAI.Analysis.WeakInfiniteness.ScalarHereditary

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

noncomputable section

open scoped CStarAlgebra Topology ComplexStarModule

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma exists_scalar_of_positive_scalars (D : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (D : Set A)] (π : A →⋆ₙₐ[ℂ] B) (k : B)
    (hp : ∀ b ∈ D,0 ≤ b → ∃ r : ℝ,π b=r • k) {x : A} (hx : x ∈ D) :
    ∃ z : ℂ,π x=z • k := by
  have hsa : ∀ b ∈ D,IsSelfAdjoint b → ∃ r : ℝ,π b=r • k := by
    intro b hb hbs
    obtain ⟨r,hr⟩ := hp b⁺ (cfcₙ_mem (·⁺ : ℝ → ℝ) hb) (CFC.posPart_nonneg b)
    obtain ⟨s,hs⟩ := hp b⁻ (cfcₙ_mem (·⁻ : ℝ → ℝ) hb) (CFC.negPart_nonneg b)
    refine ⟨r-s,?_⟩
    calc
      π b=π (b⁺-b⁻) := congrArg π (CFC.posPart_sub_negPart b hbs).symm
      _ = π b⁺-π b⁻ := map_sub π _ _
      _ = (r-s) • k := by rw [hr,hs]; module
  have hre : (ℜ x : A) ∈ D := by
    rw [realPart_apply_coe,← IsScalarTower.algebraMap_smul ℂ]
    exact SMulMemClass.smul_mem _ (add_mem hx (star_mem hx))
  have him : (ℑ x : A) ∈ D := by
    rw [imaginaryPart_apply_coe]
    apply SMulMemClass.smul_mem
    rw [← IsScalarTower.algebraMap_smul ℂ (M := A)]
    exact SMulMemClass.smul_mem _ (sub_mem hx (star_mem hx))
  obtain ⟨r,hr⟩ := hsa _ hre (ℜ x).property
  obtain ⟨s,hs⟩ := hsa _ him (ℑ x).property
  refine ⟨(r : ℂ)+Complex.I*(s : ℂ),?_⟩
  calc
    π x=π ((ℜ x : A)+Complex.I • (ℑ x : A)) := congrArg π (realPart_add_I_smul_imaginaryPart x).symm
    _ = r • k+Complex.I • (s • k) := by rw [map_add,map_smul,hr,hs]
    _ = _ := by
      rw [add_smul,mul_smul]
      change r • k+Complex.I • (s • k) =
        (algebraMap ℝ ℂ r) • k+Complex.I • ((algebraMap ℝ ℂ s) • k)
      rw [IsScalarTower.algebraMap_smul ℂ,IsScalarTower.algebraMap_smul ℂ]

lemma hereditary_image_scalar_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {x : A} (hx : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) :
    ∃ z : ℂ,π x=z • π h :=
  exists_scalar_of_positive_scalars _ π (π h)
    (fun _ hb hb0 => exists_real_scalar_of_no_orthogonal π hh hhn hno hb hb0) hx

end

end WeakPureInfiniteness
end

end OAI
