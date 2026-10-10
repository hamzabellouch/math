import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

universe u

namespace Problem346

variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- Multiplication of degree-one generators as a multilinear map. -/
def symMonomialMultilinearRaw :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymmetricAlgebra ℂ V) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)

@[simp] theorem symMonomialMultilinearRaw_apply (v : Fin n → V) :
    symMonomialMultilinearRaw n V v = symMonomialRaw n V v := rfl

/-- The tensor-power presentation of the homogeneous symmetric power. -/
def tensorToSymPowRaw :
    (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymmetricAlgebra ℂ V :=
  PiTensorProduct.lift (symMonomialMultilinearRaw n V)

@[simp] theorem tensorToSymPowRaw_tprod (v : Fin n → V) :
    tensorToSymPowRaw n V (PiTensorProduct.tprod ℂ v) = symMonomialRaw n V v :=
  PiTensorProduct.lift.tprod _

theorem tensorToSymPowRaw_range :
    LinearMap.range (tensorToSymPowRaw n V) = symPowSubmodule n V := by
  rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, tensorToSymPowRaw_tprod, symPowSubmodule]

/-- Multiplication of tensors, with codomain restricted to degree `n`. -/
def tensorToSymPow : (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymPow n V :=
  (tensorToSymPowRaw n V).codRestrict (symPowSubmodule n V) (fun x => by
    rw [← tensorToSymPowRaw_range]
    exact LinearMap.mem_range_self _ x)

@[simp] theorem tensorToSymPow_tprod (v : Fin n → V) :
    tensorToSymPow n V (PiTensorProduct.tprod ℂ v) = symMonomial n V v := by
  apply Subtype.ext
  exact tensorToSymPowRaw_tprod n V v

theorem tensorToSymPow_surjective : Function.Surjective (tensorToSymPow n V) := by
  intro x
  have hx : x.val ∈ LinearMap.range (tensorToSymPowRaw n V) := by
    rw [tensorToSymPowRaw_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

end Problem346

end

end OAI
