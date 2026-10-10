import Mathlib

namespace OAI

/-! Tensor scalar descent over finite and arbitrary Galois extensions. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace RationalHodgeCM.Partial

section BaseChange

variable {k K V : Type*} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V]

theorem one_tmul_mem_baseChange_iff (W : Submodule k V) (v : V) :
    (1 : K) ⊗ₜ[k] v ∈ W.baseChange K ↔ v ∈ W := by
  constructor
  · intro h
    have h' : (Submodule.span k ({v} : Set V)).baseChange K ≤ W.baseChange K := by
      rw [Submodule.baseChange_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact h
    exact (Submodule.baseChange_le_iff.mp h') (Submodule.subset_span (by simp))
  · exact Submodule.tmul_mem_baseChange_of_mem 1

theorem comap_baseChange (W : Submodule k V) :
    ((W.baseChange K).restrictScalars k).comap (TensorProduct.mk k K V 1) = W := by
  ext v
  exact one_tmul_mem_baseChange_iff W v

end BaseChange

section FiniteGalois

variable {k K V : Type*} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V]

def scalarConjugate (σ : K ≃ₐ[k] K) : K ⊗[k] V →ₗ[k] K ⊗[k] V :=
  σ.toLinearMap.rTensor V

@[simp]
theorem scalarConjugate_tmul (σ : K ≃ₐ[k] K) (a : K) (v : V) :
    scalarConjugate σ (a ⊗ₜ[k] v) = σ a ⊗ₜ[k] v := rfl

theorem scalarConjugate_smul (σ : K ≃ₐ[k] K) (a : K) (t : K ⊗[k] V) :
    scalarConjugate σ (a • t) = σ a • scalarConjugate σ t := by
  induction t with
  | tmul b v => simp [TensorProduct.smul_tmul', smul_eq_mul, scalarConjugate_tmul]
  | add t u ht hu => simp [smul_add, ht, hu]

def tensorTrace : K ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap ∘ₗ (Algebra.trace k K).rTensor V

@[simp]
theorem tensorTrace_tmul (a : K) (v : V) :
    tensorTrace (a ⊗ₜ[k] v) = Algebra.trace k K a • v := rfl

variable [FiniteDimensional k K] [IsGalois k K]

theorem one_tmul_tensorTrace (t : K ⊗[k] V) :
    (1 : K) ⊗ₜ[k] tensorTrace t = ∑ σ : K ≃ₐ[k] K, scalarConjugate σ t := by
  induction t with
  | tmul a v =>
      simp only [tensorTrace_tmul, scalarConjugate_tmul]
      rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add t u ht hu => simp [TensorProduct.tmul_add, Finset.sum_add_distrib, ht, hu]

def rationalPart (P : Submodule K (K ⊗[k] V)) : Submodule k V :=
  (P.restrictScalars k).comap (TensorProduct.mk k K V 1)

omit [FiniteDimensional k K] [IsGalois k K] in
@[simp]
theorem mem_rationalPart (P : Submodule K (K ⊗[k] V)) (v : V) :
    v ∈ rationalPart P ↔ (1 : K) ⊗ₜ[k] v ∈ P := Iff.rfl

theorem tensorTrace_traceDual_smul {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι k K) (i : ι) (t : K ⊗[k] V) :
    tensorTrace (b.traceDual i • t) =
      TensorProduct.equivFinsuppOfBasisLeft b t i := by
  have hcoord (a : K) : b.repr a i = Algebra.trace k K (b.traceDual i * a) := by
    simpa only [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply, mul_comm]
      using b.traceDual.traceDual_repr_apply a i
  induction t with
  | tmul a v =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, tensorTrace_tmul,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hcoord]
  | add t u ht hu => simp [smul_add, ht, hu]

theorem finite_galois_scalar_descent (P : Submodule K (K ⊗[k] V))
    (t : K ⊗[k] V) (ht : ∀ σ : K ≃ₐ[k] K, scalarConjugate σ t ∈ P) :
    t ∈ (rationalPart P).baseChange K := by
  classical
  let b := Module.Free.chooseBasis k K
  have hcoeff (i : Module.Free.ChooseBasisIndex k K) :
      TensorProduct.equivFinsuppOfBasisLeft b t i ∈ rationalPart P := by
    rw [mem_rationalPart, ← tensorTrace_traceDual_smul, one_tmul_tensorTrace]
    apply Submodule.sum_mem
    intro σ _
    rw [scalarConjugate_smul]
    exact P.smul_mem _ (ht σ)
  rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t,
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (hcoeff i)

end FiniteGalois

section ChangeCoefficients

variable {k K C V : Type*} [Field k] [Field K] [Field C]
  [Algebra k K] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
  [AddCommGroup V] [Module k V]

def coefficientInclusion : K ⊗[k] V →ₗ[K] C ⊗[k] V :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K C) (LinearMap.id : V →ₗ[k] V)

@[simp]
theorem coefficientInclusion_tmul (a : K) (v : V) :
    coefficientInclusion (C := C) (a ⊗ₜ[k] v) = algebraMap K C a ⊗ₜ[k] v := rfl

theorem coefficientInclusion_mem_baseChange (W : Submodule k V) (t : K ⊗[k] V)
    (ht : t ∈ W.baseChange K) :
    coefficientInclusion (C := C) t ∈ W.baseChange C := by
  obtain ⟨u, rfl⟩ := ht
  refine ⟨coefficientInclusion (C := C) u, ?_⟩
  induction u with
  | tmul a v => rfl
  | add u v hu hv => simp [hu, hv]

theorem rationalPart_comap_coefficientInclusion (P : Submodule C (C ⊗[k] V)) :
    rationalPart ((P.restrictScalars K).comap (coefficientInclusion (K := K))) =
      rationalPart P := by
  ext v
  simp [rationalPart, coefficientInclusion]

end ChangeCoefficients

section ArbitraryGalois

variable {k K V : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [AddCommGroup V] [Module k V]

theorem tensor_defined_over_finite_galois (t : K ⊗[k] V) :
    ∃ (L : FiniteGaloisIntermediateField k K) (u : L ⊗[k] V),
      coefficientInclusion u = t := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  let L := FiniteGaloisIntermediateField.adjoin k (↑(s.image Prod.fst) : Set K)
  have hmem (a : ↥s) : a.val.1 ∈ L.toIntermediateField := by
    exact FiniteGaloisIntermediateField.subset_adjoin k _ (Finset.mem_image.mpr
      ⟨a.val, a.property, rfl⟩)
  refine ⟨L, ∑ a : ↥s, (⟨a.val.1, hmem a⟩ : L) ⊗ₜ[k] a.val.2, ?_⟩
  simpa [coefficientInclusion, ← hs] using
    (Finset.sum_attach s (fun a : K × V => a.1 ⊗ₜ[k] a.2))

omit [IsGalois k K] in

theorem scalarConjugate_restrict (L : FiniteGaloisIntermediateField k K)
    (σ : K ≃ₐ[k] K) (u : L ⊗[k] V) :
    coefficientInclusion (scalarConjugate (σ.restrictNormal L) u) =
      scalarConjugate σ (coefficientInclusion u) := by
  induction u with
  | tmul a v =>
      simp only [scalarConjugate_tmul, coefficientInclusion_tmul,
        AlgEquiv.restrictNormal_commutes]
  | add u v hu hv => simp [hu, hv]

theorem galois_scalar_descent (P : Submodule K (K ⊗[k] V)) (t : K ⊗[k] V)
    (ht : ∀ σ : K ≃ₐ[k] K, scalarConjugate σ t ∈ P) :
    t ∈ (rationalPart P).baseChange K := by
  obtain ⟨L, u, hu⟩ := tensor_defined_over_finite_galois t
  let Q : Submodule L (L ⊗[k] V) :=
    (P.restrictScalars L).comap coefficientInclusion
  have hQ : rationalPart Q = rationalPart P :=
    rationalPart_comap_coefficientInclusion P
  have hconj (χ : L ≃ₐ[k] L) : scalarConjugate χ u ∈ Q := by
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L) K χ
    change coefficientInclusion (scalarConjugate χ u) ∈ P
    change σ.restrictNormal L = χ at hσ
    rw [← hσ, scalarConjugate_restrict, hu]
    exact ht σ
  have hdesc := finite_galois_scalar_descent Q u hconj
  rw [hQ] at hdesc
  rw [← hu]
  exact coefficientInclusion_mem_baseChange (rationalPart P) u hdesc

end ArbitraryGalois

section AmbientDescent

variable {k K C V : Type*} [Field k] [Field K] [Field C]
  [Algebra k K] [IsGalois k K] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
  [AddCommGroup V] [Module k V]

theorem scalar_descent_ambient (P : Submodule C (C ⊗[k] V)) (t : K ⊗[k] V)
    (ht : ∀ σ : K ≃ₐ[k] K, coefficientInclusion (scalarConjugate σ t) ∈ P) :
    t ∈ (rationalPart P).baseChange K := by
  let Q : Submodule K (K ⊗[k] V) :=
    (P.restrictScalars K).comap coefficientInclusion
  have hQ : rationalPart Q = rationalPart P := rationalPart_comap_coefficientInclusion P
  have hdesc := galois_scalar_descent Q t ht
  rwa [hQ] at hdesc

end AmbientDescent

abbrev AlgebraicNumbers := algebraicClosure ℚ ℂ

theorem trace_descent {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℂ (ℂ ⊗[ℚ] V)) (t : AlgebraicNumbers ⊗[ℚ] V)
    (ht : ∀ σ : AlgebraicNumbers ≃ₐ[ℚ] AlgebraicNumbers,
      coefficientInclusion (scalarConjugate σ t) ∈ P) :
    t ∈ (rationalPart P).baseChange AlgebraicNumbers := by
  let : IsAlgClosure ℚ AlgebraicNumbers := algebraicClosure.isAlgClosure ℚ ℂ
  exact scalar_descent_ambient P t ht

end RationalHodgeCM.Partial

end

end OAI
