import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.PositiveExtension

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def saSubmodule (S : Submodule ℂ A) : Submodule ℝ (selfAdjoint A) where
  carrier := {x | (x : A) ∈ S}
  zero_mem' := S.zero_mem
  add_mem' hx hy := S.add_mem hx hy
  smul_mem' r x hx := by
    change r • (x : A) ∈ S
    rw [← Complex.coe_smul]
    exact S.smul_mem (r : ℂ) hx

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma saSubmodule_mem (S : Submodule ℂ A) (x : selfAdjoint A) :
    x ∈ saSubmodule S ↔ (x : A) ∈ S := Iff.rfl

def saUnit (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) : saSubmodule S := ⟨1,h1⟩

lemma positive_real_bound (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : saSubmodule S →ₗ[ℝ] ℝ)
    (hf : ∀ x : saSubmodule S, 0 ≤ ((x : selfAdjoint A) : A) → 0 ≤ f x)
    (x : saSubmodule S) : ‖f x‖ ≤ f (saUnit S h1) * ‖x‖ := by
  have upper (y : saSubmodule S) : f y ≤ ‖y‖ * f (saUnit S h1) := by
    have hy : 0 ≤ (((‖y‖ • saUnit S h1 - y : saSubmodule S) : selfAdjoint A) : A) := by
      change 0 ≤ ‖y‖ • (1 : A) - (y : selfAdjoint A)
      rw [sub_nonneg,← Algebra.algebraMap_eq_smul_one]
      exact (y : selfAdjoint A).property.le_algebraMap_norm_self
    have hh := hf (‖y‖ • saUnit S h1-y) hy
    simp only [map_sub,map_smul,smul_eq_mul] at hh
    linarith
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · have hh := upper (-x)
    rw [map_neg] at hh
    change -f x ≤ ‖-((x : selfAdjoint A) : A)‖ * f (saUnit S h1) at hh
    rw [norm_neg] at hh
    change -(f (saUnit S h1)*‖((x : selfAdjoint A) : A)‖) ≤ f x
    nlinarith
  · simpa [mul_comm] using upper x

theorem exists_real_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : saSubmodule S →ₗ[ℝ] ℝ)
    (hf : ∀ x : saSubmodule S, 0 ≤ ((x : selfAdjoint A) : A) → 0 ≤ f x) :
    ∃ g : selfAdjoint A →L[ℝ] ℝ,
      (∀ x : saSubmodule S, g x=f x) ∧
      (∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x) := by
  let c := f (saUnit S h1)
  have hc : 0 ≤ c := hf _ zero_le_one
  let fc : saSubmodule S →L[ℝ] ℝ := f.mkContinuous c (positive_real_bound S h1 f hf)
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq (saSubmodule S) fc
  have hgc : ‖g‖ ≤ c := by
    rw [hgn]
    exact LinearMap.mkContinuous_norm_le _ hc _
  have hg1 : g 1=c := hg (saUnit S h1)
  refine ⟨g,hg,?_⟩
  intro x hx
  let b : selfAdjoint A := ‖x‖ • 1-x
  have hb : 0 ≤ (b : A) := by
    change 0 ≤ ‖x‖ • (1 : A) - (x : A)
    rw [sub_nonneg,← Algebra.algebraMap_eq_smul_one]
    exact x.property.le_algebraMap_norm_self
  have hbn : ‖b‖ ≤ ‖x‖ := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap (b : A) (norm_nonneg _) hb).mpr
    change ‖x‖ • (1 : A) - (x : A) ≤ algebraMap ℝ A ‖x‖
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ hx
  have hgub : g b ≤ c*‖x‖ := calc
    g b ≤ ‖g b‖ := Real.le_norm_self _
    _ ≤ ‖g‖*‖b‖ := g.le_opNorm b
    _ ≤ c*‖x‖ := mul_le_mul hgc hbn (norm_nonneg _) hc
  simp only [b,map_sub,map_smul,hg1,smul_eq_mul] at hgub
  nlinarith

end Kadison.PositiveExtension

end

end
end

end OAI
