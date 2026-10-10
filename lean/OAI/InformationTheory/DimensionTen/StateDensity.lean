import OAI.Analysis.Quantum.DimensionTen.Main
import OAI.InformationTheory.SecretKey.Main

namespace OAI

/-! Normalization and product-free range of the dimension-ten Choi state. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped ComplexOrder Kronecker ENNReal

namespace DimensionTen
universe u

lemma compositeChoi_trace_ne : trace compositeChoi ≠ 0 :=
  fun h => compositeChoi_ne (compositeChoi_posSemidef.trace_eq_zero_iff.mp h)

lemma compositeChoi_trace_nonneg : 0 ≤ trace compositeChoi :=
  compositeChoi_posSemidef.trace_nonneg

lemma compositeChoi_trace_re : ((trace compositeChoi).re : ℂ) = trace compositeChoi := by
  have hi := (RCLike.nonneg_iff.mp compositeChoi_trace_nonneg).2
  apply Complex.ext
  · rfl
  · exact hi.symm

def rho : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  (trace compositeChoi)⁻¹ • compositeChoi

lemma rho_density : ZeroKey.Density rho := by
  constructor
  · exact compositeChoi_posSemidef.smul (inv_nonneg.mpr compositeChoi_trace_nonneg)
  · rw [rho, Matrix.trace_smul, smul_eq_mul,
      inv_mul_cancel₀ compositeChoi_trace_ne]

lemma rho_productfree (u v : Fin 10 → ℂ) (w : Fin 10 × Fin 10 → ℂ)
    (h : rho *ᵥ w = productVector u v) : u = 0 ∨ v = 0 := by
  apply compositeChoi_productfree u v ((trace compositeChoi)⁻¹ • w)
  simpa only [rho, Matrix.smul_mulVec, Matrix.mulVec_smul] using h

lemma operational_separable {a b : ℕ}
    (Z : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (h : ZeroKey.Separable Z) : separable Z := by
  obtain ⟨r,A,B,hA,hB,he⟩ := h
  exact ⟨r,A,B,fun i => ⟨hA i,hB i⟩,he⟩

lemma rho_entangled : ¬ ZeroKey.Separable rho := by
  intro h
  have hz := h.smul compositeChoi_trace_nonneg
  rw [rho, smul_smul, mul_inv_cancel₀ compositeChoi_trace_ne, one_smul] at hz
  exact compositeChoi_not_separable (operational_separable _ hz)

lemma rho_range_contains_no_nonzero_product :
    ∀ u v : Fin 10 → ℂ,
      productVector u v ∈ Set.range (fun w => rho *ᵥ w) → productVector u v = 0 := by
  intro u v ⟨w,hw⟩
  rcases rho_productfree u v w hw with rfl | rfl <;>
    ext i <;> simp [productVector]

theorem main_state_geometry :
    ZeroKey.Density rho ∧ ¬ ZeroKey.Separable rho ∧
      (∀ u v : Fin 10 → ℂ,
        productVector u v ∈ Set.range (fun w => rho *ᵥ w) → productVector u v = 0) := by
  exact ⟨rho_density, rho_entangled, rho_range_contains_no_nonzero_product⟩

end DimensionTen

end

end OAI
